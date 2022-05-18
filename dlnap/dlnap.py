#!/usr/bin/python

# @file dlnap.py
# @author cherezov.pavel@gmail.com
# @brief Python over the network media player to playback on DLNA UPnP devices.

# Change log:
#   0.1  initial version.
#   0.2  device renamed to DlnapDevice; DLNAPlayer is disappeared.
#   0.3  debug output is added. Extract location url fixed.
#   0.4  compatible discover mode added.
#   0.5  xml parser introduced for device descriptions
#   0.6  xpath introduced to navigate over xml dictionary
#   0.7  device ip argument introduced
#   0.8  debug output is replaced with standard logging
#   0.9  pause/stop added. Video playback tested on Samsung TV
#   0.10 proxy (draft) is introduced.
#   0.11 sync proxy for py2 and py3 implemented, --proxy-port added
#   0.12 local files can be played as well now via proxy
#   0.13 ssdp protocol version argument added
#   0.14 fixed bug with receiving responses from device
#   0.15 Lot's of fixes and features added thanks @ttopholm and @NicoPy
#   0.16 migrate from getopt to argparse for argument parsing
#
#   1.0  moved from idea version

__version__ = "0.16"

import argparse
import re
import sys
import time
import signal
import socket
import select
import logging
import traceback
import mimetypes
from contextlib import contextmanager

import os
from urllib.request import urlopen
from http.server import HTTPServer
from http.server import BaseHTTPRequestHandler

import shutil
import threading

SSDP_GROUP = ("239.255.255.250", 1900)
URN_AVTransport = "urn:schemas-upnp-org:service:AVTransport:1"
URN_AVTransport_Fmt = "urn:schemas-upnp-org:service:AVTransport:{}"

URN_RenderingControl = "urn:schemas-upnp-org:service:RenderingControl:1"
URN_RenderingControl_Fmt = "urn:schemas-upnp-org:service:RenderingControl:{}"

SSDP_ALL = "ssdp:all"

def _get_xml_tag_value(x, i=0):
   x = x.strip()
   value = ''
   tag = ''

   # skip <? > tag
   if x[i:].startswith('<?'):
      i += 2
      while i < len(x) and x[i] != '<':
         i += 1

   # check for empty tag like '</tag>'
   if x[i:].startswith('</'):
      i += 2
      in_attr = False
      while i < len(x) and x[i] != '>':
         if x[i] == ' ':
            in_attr = True
         if not in_attr:
            tag += x[i]
         i += 1
      return (tag.strip(), '', x[i+1:])

   # not an xml, treat like a value
   if not x[i:].startswith('<'):
      return ('', x[i:], '')

   i += 1 # <

   # read first open tag
   in_attr = False
   while i < len(x) and x[i] != '>':
      # get rid of attributes
      if x[i] == ' ':
         in_attr = True
      if not in_attr:
         tag += x[i]
      i += 1

   i += 1 # >

   # replace self-closing <tag/> by <tag>None</tag>
   empty_elmt = '<' + tag + ' />'
   closed_elmt = '<' + tag + '>None</'+tag+'>'
   if x.startswith(empty_elmt):
      x = x.replace(empty_elmt, closed_elmt)

   while i < len(x):
      value += x[i]
      if x[i] == '>' and value.endswith('</' + tag + '>'):
         # Note: will not work with xml like <a> <a></a> </a>
         close_tag_len = len(tag) + 2 # />
         value = value[:-close_tag_len]
         break
      i += 1
   return (tag.strip(), value[:-1], x[i+1:])

def _xml2dict(s, ignoreUntilXML=False):
   if ignoreUntilXML:
      s = ''.join(re.findall(".*?(<.*)", s, re.M))

   d = {}
   while s:
      tag, value, s = _get_xml_tag_value(s)
      value = value.strip()
      isXml, dummy, dummy2 = _get_xml_tag_value(value)
      if tag not in d:
         d[tag] = []
      if not isXml:
         if not value:
            continue
         d[tag].append(value.strip())
      else:
         if tag not in d:
            d[tag] = []
         d[tag].append(_xml2dict(value))
   return d

def _xpath(d, path):
   """ Return value from xml dictionary at path.

   d -- xml dictionary
   path -- string path like root/device/serviceList/service@serviceType=URN_AVTransport/controlURL
   return -- value at path or None if path not found
   """

   for p in path.split('/'):
      tag_attr = p.split('@')
      tag = tag_attr[0]
      if tag not in d:
         return None

      attr = tag_attr[1] if len(tag_attr) > 1 else ''
      if attr:
         a, aval = attr.split('=')
         for s in d[tag]:
            if s[a] == [aval]:
               d = s
               break
      else:
         d = d[tag][0]
   return d

class HttpException(Exception):
   pass

running = False
class DownloadProxy(BaseHTTPRequestHandler):

   def log_message(self, format, *args):
      pass

   def log_request(self, code='-', size='-'):
      pass

   def response_success(self):
      url = self.path[1:] # replace '/'

      if os.path.exists(url):
         f = open(url, mode="rb")
         content_type = mimetypes.guess_type(url)[0]
      else:
         f = urlopen(url=url)
         content_type = f.getheader("Content-Type")

      self.send_response(200, "ok")
      self.send_header('Access-Control-Allow-Origin', '*')
      self.send_header('Access-Control-Allow-Methods', 'GET, OPTIONS')
      self.send_header("Access-Control-Allow-Headers", "X-Requested-With")
      self.send_header("Access-Control-Allow-Headers", "Content-Type")
      self.send_header("Content-Type", content_type)
      self.end_headers()

   def do_OPTIONS(self):
      self.response_success()

   def do_HEAD(self):
      self.response_success()

   def do_GET(self):
      global running
      url = self.path[1:] # replace '/'

      content_type = ''
      if os.path.exists(url):
         f = open(url, mode="rb")
         content_type = mimetypes.guess_type(url)[0]
         size = os.path.getsize(url)
      elif not url or not url.startswith('http'):
         self.response_success()
         return
      else:
         f = urlopen(url=url)

      try:
         if not content_type:
             content_type = f.getheader("Content-Type")
             size = f.getheader("Content-Length")

         self.send_response(200)
         self.send_header('Access-Control-Allow-Origin', '*')
         self.send_header("Content-Type", content_type)
         self.send_header(f"Content-Disposition", 'attachment; filename="{os.path.basename(url)}"')
         self.send_header("Content-Length", str(size))
         self.end_headers()
         shutil.copyfileobj(f, self.wfile)
      finally:
         running = False
         f.close()

def runProxy(ip = '', port=8000):
   global running
   running = True
   DownloadProxy.protocol_version = "HTTP/1.0"
   httpd = HTTPServer((ip, port), DownloadProxy)
   while running:
      httpd.handle_request()

def _get_port(url):
   port = re.findall('http://.*?:(\d+).*', url)
   return int(port[0]) if port else 80


def _get_control_url(xml, urn):
   "Extract AVTransport contol url from device description xml"
   return _xpath(xml, f'root/device/serviceList/service@serviceType={urn}/controlURL')

@contextmanager
def _send_udp(to, packet):
   """ Send UDP message to group

   to -- (host, port) group to send the packet to
   packet -- message to send
   """
   sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM, socket.IPPROTO_UDP)
   sock.sendto(packet.encode(), to)
   yield sock
   sock.close()

def _unescape_xml(xml):
   "Replace escaped xml symbols with real ones."
   return xml.replace('&lt;', '<').replace('&gt;', '>').replace('&quot;', '"')

def _send_tcp(to, payload):
   """ Send TCP message to group

   to -- (host, port) group to send to payload to
   payload -- message to send
   """
   try:
      sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
      sock.settimeout(5)
      sock.connect(to)
      sock.sendall(payload.encode('utf-8'))

      data = sock.recv(2048)
      data = data.decode('utf-8')
      if not data.startswith("HTTP/1.1 200 OK"):
         raise HttpException(f"Oops, there was a problem... server response is:\n{data}")
      data = _xml2dict(_unescape_xml(data), True)

      errorDescription = _xpath(data, 's:Envelope/s:Body/s:Fault/detail/UPnPError/errorDescription')
      if errorDescription is not None:
         logging.error(errorDescription)
   except Exception as e:
      data = ''
   finally:
      sock.close()
   return data


def _get_location_url(raw):
    "Extract device description url from discovery response"
    t = re.findall('\n(?i)location:\s*(.*)\r\s*', raw, re.M)
    if len(t) > 0:
        return t[0]
    return ''

def _get_friendly_name(xml):
   "Extract device name from description xml"
   name = _xpath(xml, 'root/device/friendlyName')
   return name if name is not None else 'Unknown'

def _get_serve_ip(target_ip, target_port=80):
    """ Find ip address of network interface used to communicate with target

    target-ip -- ip address of target
    return -- ip address of interface connected to target
    """
    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    s.connect((target_ip, target_port))
    my_ip = s.getsockname()[0]
    s.close()
    return my_ip

class DlnapDevice:
   """ Represents DLNA/UPnP device.
   """

   def __init__(self, raw, ip):
      self.__logger = logging.getLogger(self.__class__.__name__)
      self.__logger.info(f'=> New DlnapDevice (ip = {ip}) initialization..')

      self.ip = ip
      self.ssdp_version = 1

      self.port = None
      self.name = 'Unknown'
      self.control_url = None
      self.rendering_control_url = None
      self.has_av_transport = False

      try:
         self.__raw = raw.decode()
         self.location = _get_location_url(self.__raw)
         self.__logger.info(f'location: {self.location}')

         self.port = _get_port(self.location)
         self.__logger.info(f'port: {self.port}')

         raw_desc_xml = urlopen(self.location).read().decode()

         self.__desc_xml = _xml2dict(raw_desc_xml)
         self.__logger.debug(f'description xml: {self.__desc_xml}')

         self.name = _get_friendly_name(self.__desc_xml)
         self.__logger.info(f'friendlyName: {self.name}')

         self.control_url = _get_control_url(self.__desc_xml, URN_AVTransport)
         self.__logger.info(f'control_url: {self.control_url}')

         self.rendering_control_url = _get_control_url(self.__desc_xml, URN_RenderingControl)
         self.__logger.info(f'rendering_control_url: {self.rendering_control_url}')

         self.has_av_transport = self.control_url is not None
         self.__logger.info('=> Initialization completed')
      except Exception as e:
         self.__logger.warning(f'DlnapDevice (ip = {ip}) init exception:\n{traceback.format_exc()}')

   def __repr__(self):
      return f'{self.name} @ {self.ip}'

   def __eq__(self, d):
      return self.name == d.name and self.ip == d.ip

   def _payload_from_template(self, action, data, urn):
      fields = ''
      for tag, value in data.items():
        fields += f'<{tag}>{value}</{tag}>'

      payload = f"""<?xml version="1.0" encoding="utf-8"?>
         <s:Envelope xmlns:s="http://schemas.xmlsoap.org/soap/envelope/" s:encodingStyle="http://schemas.xmlsoap.org/soap/encoding/">
            <s:Body>
               <u:{action} xmlns:u="{urn}">
                  {fields}
               </u:{action}>
            </s:Body>
         </s:Envelope>"""
      return payload

   def _create_packet(self, action, data):
      if action in ["SetVolume", "SetMute", "GetVolume"]:
          url = self.rendering_control_url
          urn = URN_RenderingControl_Fmt.format(self.ssdp_version)
      else:
          url = self.control_url
          urn = URN_AVTransport_Fmt.format(self.ssdp_version)
      payload = self._payload_from_template(action=action, data=data, urn=urn)

      packet = "\r\n".join([
         f'POST {url} HTTP/1.1',
         f'User-Agent: {__file__}/{__version__}',
         'Accept: */*',
         'Content-Type: text/xml; charset="utf-8"',
         f'HOST: {self.ip}:{self.port}',
         f'Content-Length: {len(payload)}',
         f'SOAPACTION: "{urn}#{action}"',
         'Connection: close',
         '',
         payload,
         ])

      self.__logger.debug(packet)
      return packet

   def set_current_media(self, url, instance_id=0):
      packet = self._create_packet('SetAVTransportURI', {'InstanceID':instance_id, 'CurrentURI':url, 'CurrentURIMetaData':'' })
      _send_tcp((self.ip, self.port), packet)

   def play(self, instance_id=0):
      packet = self._create_packet('Play', {'InstanceID': instance_id, 'Speed': 1})
      _send_tcp((self.ip, self.port), packet)

   def pause(self, instance_id=0):
      packet = self._create_packet('Pause', {'InstanceID': instance_id, 'Speed':1})
      _send_tcp((self.ip, self.port), packet)

   def stop(self, instance_id=0):
      packet = self._create_packet('Stop', {'InstanceID': instance_id, 'Speed': 1})
      _send_tcp((self.ip, self.port), packet)

   def seek(self, position, instance_id = 0):
      packet = self._create_packet('Seek', {'InstanceID':instance_id, 'Unit':'REL_TIME', 'Target': position })
      _send_tcp((self.ip, self.port), packet)

   def volume(self, volume=10, instance_id = 0):
      packet = self._create_packet('SetVolume', {'InstanceID': instance_id, 'DesiredVolume': volume, 'Channel': 'Master'})
      _send_tcp((self.ip, self.port), packet)

   def get_volume(self, instance_id=0):
      packet = self._create_packet('GetVolume', {'InstanceID':instance_id, 'Channel': 'Master'})
      _send_tcp((self.ip, self.port), packet)

   def mute(self, instance_id=0):
      packet = self._create_packet('SetMute', {'InstanceID': instance_id, 'DesiredMute': '1', 'Channel': 'Master'})
      _send_tcp((self.ip, self.port), packet)

   def unmute(self, instance_id=0):
      packet = self._create_packet('SetMute', {'InstanceID': instance_id, 'DesiredMute': '0', 'Channel': 'Master'})
      _send_tcp((self.ip, self.port), packet)

   def info(self, instance_id=0):
      packet = self._create_packet('GetTransportInfo', {'InstanceID': instance_id})
      return _send_tcp((self.ip, self.port), packet)

   def media_info(self, instance_id=0):
      packet = self._create_packet('GetMediaInfo', {'InstanceID': instance_id})
      return _send_tcp((self.ip, self.port), packet)

   def position_info(self, instance_id=0):
      packet = self._create_packet('GetPositionInfo', {'InstanceID': instance_id})
      return _send_tcp((self.ip, self.port), packet)

   def set_next(self, url):
      pass

   def next(self):
      pass

def discover(name='', ip='', timeout=1, st=SSDP_ALL, mx=3, ssdp_version=1):
   """ Discover UPnP devices in the local network.

   name -- name or part of the name to filter devices
   timeout -- timeout to perform discover
   st -- st field of discovery packet
   mx -- mx field of discovery packet
   return -- list of DlnapDevice
   """
   st = st.format(ssdp_version)
   payload = "\r\n".join([
              'M-SEARCH * HTTP/1.1',
              f'User-Agent: {__file__}/{__version__}'.format(__file__, __version__),
              'HOST: {}:{}'.format(*SSDP_GROUP),
              'Accept: */*',
              'MAN: "ssdp:discover"',
              f'ST: {st}',
              f'MX: {mx}',
              '',
              ''])
   devices = []
   with _send_udp(SSDP_GROUP, payload) as sock:
      start = time.time()
      while True:
         if time.time() - start > timeout:
            # timed out
            break
         r, w, x = select.select([sock], [], [sock], 1)
         if sock in r:
             data, addr = sock.recvfrom(1024)
             if ip and addr[0] != ip:
                continue

             d = DlnapDevice(data, addr[0])
             d.ssdp_version = ssdp_version
             if d not in devices:
                if not name or name is None or name.lower() in d.name.lower():
                   if not ip:
                      devices.append(d)
                   elif d.has_av_transport:
                      # no need in further searching by ip
                      devices.append(d)
                      break

         elif sock in x:
             raise Exception('Getting response failed')
         else:
             # Nothing to read
             pass
   return devices

def signal_handler(signal, frame):
   print(' Got Ctrl + C, exit now!')
   sys.exit(1)

signal.signal(signal.SIGINT, signal_handler)

if __name__ == '__main__':
   parser = argparse.ArgumentParser()
   parser.add_argument("--ip", type=str,
                       help="ip address for faster access to the known device.")
   parser.add_argument("--device", "-d", type=str,
		       help="discover devices with this name as substring")
   parser.add_argument("--all", action="store_true",
                       help="flag to discover all upnp devices, not only devices with AVTransport ability")
   parser.add_argument("--volume", type=int, default=10,
                       help="set current volume for playback.")
   parser.add_argument("--seek", type=str, default='00:00:00',
                       help="<position in HH:MM:SS> - set current position for playback.")
   parser.add_argument("--timeout", default=None, type=float,
                       help="discover timeout.")
   parser.add_argument("--ssdp-version", default=1, type=int,
                       help="discover devices by protocol version.")
   parser.add_argument("--proxy", action="store_true",
                       help="use local proxy on proxy port.")
   parser.add_argument("--proxy-port", type=int, default=8000,
                       help="proxy port to listen incomming connections from devices.")
   parser.add_argument("--action", type=str, default='list', choices=['play', 'stop', 'pause', 'mute', 'unmute', 'list', 'info', 'media-info'],
                       help="select the action you want to perform")
   parser.add_argument("--url", type=str,
                       help="To be used along with 'play' action - the url to be played")
   parser.add_argument("--verbosity", type=str, choices=[None, 'info', 'warn', 'debug'], default=None,
                       help="select the level of verbosity.")
   parser.add_argument("--version", action="store_true",
                       help="display the current version of this tool")

   args = parser.parse_args()

   compatibleOnly = True

   if args.version:
      print(__version__)
      sys.exit(0)

   if args.verbosity == 'debug':
      logLevel = logging.DEBUG
   elif args.verbosity == 'info':
      logLevel = logging.INFO
   else:
      logLevel = logging.WARN

   timeout = args.timeout
   if args.all:
      compatibleOnly = False
   elif args.ip:
      compatibleOnly = False
      timeout = 10
      if args.action == "play":
         assert args.url, "Please specify the URL to the media you want to play with '--url'"

   logging.basicConfig(level=logLevel)

   st = URN_AVTransport_Fmt if compatibleOnly else SSDP_ALL
   allDevices = discover(name=args.device, ip=args.ip, timeout=timeout, st=st, ssdp_version=args.ssdp_version)
   if not allDevices:
      print('No compatible devices found.')
      sys.exit(1)

   if args.action == 'list':
      print('Discovered devices:')
      for d in allDevices:
         print(' {} {d}'.format('[a]' if d.has_av_transport else '[x]'))
      sys.exit(0)

   d = allDevices[0]
   print(d)

   if args.url.lower().replace('https://', '').replace('www.', '').startswith('youtube.'):
      import subprocess
      process = subprocess.Popen(['youtube-dl', '-g', url], stdout = subprocess.PIPE)
      args.url, err = process.communicate()

   if args.url.lower().startswith('https://'):
      args.proxy = True

   if args.proxy:
      args.ip = _get_serve_ip(d.ip)
      t = threading.Thread(target=runProxy, kwargs={'ip' : args.ip, 'port' : args.proxy_port})
      t.daemon = True
      t.start()
      time.sleep(2)

   if args.action == 'play':
      try:
         try:
            d.stop()
         except HttpException:
            # It might fail when there were no media being played - just ignore this specific case
            pass
         args.url = f'http://{args.ip}:{args.proxy_port}/{args.url}' if args.proxy else args.url
         d.set_current_media(url=args.url)
         d.play()
      except Exception as e:
         print('Device is unable to play media.')
         logging.warn(f'Play exception:\n{traceback.format_exc()}')
         sys.exit(1)
   elif args.action == 'pause':
      d.pause()
   elif args.action == 'stop':
      d.stop()
   elif args.action == 'volume':
      d.volume(vol)
   elif args.action == 'seek':
      d.seek(position)
   elif args.action == 'mute':
      d.mute()
   elif args.action == 'unmute':
      d.unmute()
   elif args.action == 'info':
      print(d.info())
   elif args.action == 'media-info':
      print(d.media_info())

   if args.proxy:
      while running:
         time.sleep(30)
