import atexit
import cPickle as pickle
import errno
import fnmatch
import io
import os
import os.path
import picamera
import pygame
import stat
import threading
import time
import yuv2rgb
from pygame.locals import *
from subprocess import call  
import traceback
import sys
from PIL import Image as PILImage
from PIL import ImageFilter
from PIL import ImageOps
from PIL import ImageDraw
from PIL import ImageEnhance

from Adafruit_Thermal import *

# UI classes ---------------------------------------------------------------

# Small resistive touchscreen is best suited to simple tap interactions.
# Importing a big widget library seemed a bit overkill.  Instead, a couple
# of rudimentary classes are sufficient for the UI elements:

# Icon is a very simple bitmap class, just associates a name and a pygame
# image (PNG loaded from icons directory) for each.
# There isn't a globally-declared fixed list of Icons.  Instead, the list
# is populated at runtime from the contents of the 'icons' directory.

class Icon:

	def __init__(self, name):
	  self.name = name
	  try:
	    self.bitmap = pygame.image.load(iconPath + '/' + name + '.png')
	  except:
	    pass

# Button is a simple tappable screen region.  Each has:
#  - bounding rect ((X,Y,W,H) in pixels)
#  - optional background color and/or Icon (or None), always centered
#  - optional foreground Icon, always centered
#  - optional single callback function
#  - optional single value passed to callback
# Occasionally Buttons are used as a convenience for positioning Icons
# but the taps are ignored.  Stacking order is important; when Buttons
# overlap, lowest/first Button in list takes precedence when processing
# input, and highest/last Button is drawn atop prior Button(s).  This is
# used, for example, to center an Icon by creating a passive Button the
# width of the full screen, but with other buttons left or right that
# may take input precedence (e.g. the Effect labels & buttons).
# After Icons are loaded at runtime, a pass is made through the global
# buttons[] list to assign the Icon objects (from names) to each Button.

class Button:

	def __init__(self, rect, **kwargs):
	  self.rect     = rect # Bounds
	  self.color    = None # Background fill color, if any
	  self.iconBg   = None # Background Icon (atop color fill)
	  self.iconFg   = None # Foreground Icon (atop background)
	  self.bg       = None # Background Icon name
	  self.fg       = None # Foreground Icon name
	  self.callback = None # Callback function
	  self.value    = None # Value passed to callback
	  for key, value in kwargs.iteritems():
	    if   key == 'color': self.color    = value
	    elif key == 'bg'   : self.bg       = value
	    elif key == 'fg'   : self.fg       = value
	    elif key == 'cb'   : self.callback = value
	    elif key == 'value': self.value    = value

	def selected(self, pos):
	  x1 = self.rect[0]
	  y1 = self.rect[1]
	  x2 = x1 + self.rect[2] - 1
	  y2 = y1 + self.rect[3] - 1
	  if ((pos[0] >= x1) and (pos[0] <= x2) and
	      (pos[1] >= y1) and (pos[1] <= y2)):
	    if self.callback:
	      if self.value is None: self.callback()
	      else:                  self.callback(self.value)
	    return True
	  return False

	def draw(self, screen):
	  if self.color:
	    screen.fill(self.color, self.rect)
	  if self.iconBg:
	    screen.blit(self.iconBg.bitmap,
	      (self.rect[0]+(self.rect[2]-self.iconBg.bitmap.get_width())/2,
	       self.rect[1]+(self.rect[3]-self.iconBg.bitmap.get_height())/2))
	  if self.iconFg:
	    screen.blit(self.iconFg.bitmap,
	      (self.rect[0]+(self.rect[2]-self.iconFg.bitmap.get_width())/2,
	       self.rect[1]+(self.rect[3]-self.iconFg.bitmap.get_height())/2))

	def setBg(self, name):
	  if name is None:
	    self.iconBg = None
	  else:
	    for i in icons:
	      if name == i.name:
	        self.iconBg = i
	        break


# UI callbacks -------------------------------------------------------------
# These are defined before globals because they're referenced by items in
# the global buttons[] list.

def settingCallback(n): # Pass 1 (next setting) or -1 (prev setting)
	global screenMode
	screenMode += n
	if screenMode < 4:               screenMode = len(buttons) - 1
	elif screenMode >= len(buttons): screenMode = 4

def fxCallback(n): # Pass 1 (next effect) or -1 (prev effect)
	global fxMode
	setFxMode((fxMode + n) % len(fxData))

def quitCallback(): # Quit confirmation button
	saveSettings()
	raise SystemExit

def viewCallback(n): # Viewfinder buttons
	global loadIdx, scaled, screenMode, screenModePrior, settingMode

	if n is 0:   # Gear icon (settings)
	  screenMode = settingMode # Switch to last settings mode
	elif n is 1: # Play icon (image playback)
	  if scaled: # Last photo is already memory-resident
	    loadIdx         = saveIdx
	    screenMode      =  0 # Image playback
	    screenModePrior = -1 # Force screen refresh
	  else:      # Load image
	    r = imgRange(pathData)
	    if r: showImage(r[1]) # Show last image in directory
	    else: screenMode = 2  # No images
	else: # Rest of screen = shutter
	  takePicture()

def doneCallback(): # Exit settings
	global screenMode, settingMode
	if screenMode > 3:
	  settingMode = screenMode
	  saveSettings()
	screenMode = 3 # Switch back to viewfinder mode

def imageCallback(n): # Pass 1 (next image), -1 (prev image) or 0 (delete)
	global screenMode
	if n is 0:
	  screenMode = 1 # Delete confirmation
	else:
	  showNextImage(n)

def deleteCallback(n): # Delete confirmation
	global loadIdx, scaled, screenMode
	screenMode      =  0
	screenModePrior = -1
	if n is True:
	  os.remove(pathData + '/IMG_' + '%04d' % loadIdx + '.JPG')
	  if(imgRange(pathData)):
	    screen.fill(0)
	    pygame.display.update()
	    showNextImage(-1)
	  else: # Last image deleteted; go to 'no images' mode
	    screenMode = 2
	    scaled     = None
	    loadIdx    = -1




# Global stuff -------------------------------------------------------------

screenMode      =  3      # Current screen mode; default = viewfinder
screenModePrior = -1      # Prior screen mode (for detecting changes)
settingMode     =  4      # Last-used settings mode (default = storage)
fxMode          =  0      # Image effect; default = Normal
iconPath        = '/home/pi/PiCam/icons' # Subdirectory containing UI bitmaps (PNG format)
saveIdx         = -1      # Image index for saving (-1 = none set yet)
loadIdx         = -1      # Image index for loading
scaled          = None    # pygame Surface w/last-loaded image

sizeData = [(1296, 972), (320, 240), (0.0, 0.0, 1.0, 1.0)]

# A fixed list of image effects is used (rather than polling
# camera.IMAGE_EFFECTS) because the latter contains a few elements
# that aren't valid (at least in video_port mode) -- e.g. blackboard,
# whiteboard, posterize (but posterise, British spelling, is OK).
# Others have no visible effect (or might require setting add'l
# camera parameters for which there's no GUI yet) -- e.g. saturation,
# colorbalance, colorpoint.
fxData = [
  'none', 'sketch', 'gpen', 'pastel', 'watercolor', 'oilpaint', 'hatch',
  'negative', 'colorswap', 'posterise', 'denoise', 'blur', 'film',
  'washedout', 'emboss', 'cartoon', 'solarize' ]

pathData = '/home/pi/Photos'

icons = [] # This list gets populated at startup

# buttons[] is a list of lists; each top-level list element corresponds
# to one screen mode (e.g. viewfinder, image playback, storage settings),
# and each element within those lists corresponds to one UI button.
# There's a little bit of repetition (e.g. prev/next buttons are
# declared for each settings screen, rather than a single reusable
# set); trying to reuse those few elements just made for an ugly
# tangle of code elsewhere.

buttons = [
  # Screen mode 0 is photo playback
  [Button((  0,188,320, 52), bg='done' , cb=doneCallback),
   Button((  0,  0, 80, 52), bg='prev' , cb=imageCallback, value=-1),
   Button((240,  0, 80, 52), bg='next' , cb=imageCallback, value= 1),
   Button(( 88, 70,157,102)), # 'Working' label (when enabled)
   Button((148,129, 22, 22)), # Spinner (when enabled)
   Button((121,  0, 78, 52), bg='trash', cb=imageCallback, value= 0)],

  # Screen mode 1 is delete confirmation
  [Button((  0,35,320, 33), bg='delete'),
   Button(( 32,86,120,100), bg='yn', fg='yes',
    cb=deleteCallback, value=True),
   Button((168,86,120,100), bg='yn', fg='no',
    cb=deleteCallback, value=False)],

  # Screen mode 2 is 'No Images'
  [Button((0,  0,320,240), cb=doneCallback), # Full screen = button
   Button((0,188,320, 52), bg='done'),       # Fake 'Done' button
   Button((0, 53,320, 80), bg='empty')],     # 'Empty' message

  # Screen mode 3 is viewfinder / snapshot
  [Button((  0,188,156, 52), bg='gear', cb=viewCallback, value=0),
  
   Button((  0,  0,320,240)           , cb=viewCallback, value=2),
   Button(( 88, 51,157,102)),  # 'Working' label (when enabled)
   Button((148, 110,22, 22))], # Spinner (when enabled)

  # Remaining screens are settings modes

  # Screen mode 4 is graphic effect
  [Button((  0,188,320, 52), bg='done', cb=doneCallback),
   Button((  0,  0, 80, 52), bg='prev', cb=settingCallback, value=-1),
   Button((240,  0, 80, 52), bg='next', cb=settingCallback, value= 1),
   Button((  0, 70, 80, 52), bg='prev', cb=fxCallback     , value=-1),
   Button((240, 70, 80, 52), bg='next', cb=fxCallback     , value= 1),
   Button((  0, 67,320, 91), bg='fx-none'),
   Button((  0, 11,320, 29), bg='fx')],

  # Screen mode 5 is quit confirmation
  [Button((  0,188,320, 52), bg='done'   , cb=doneCallback),
   Button((  0,  0, 80, 52), bg='prev'   , cb=settingCallback, value=-1),
   Button((240,  0, 80, 52), bg='next'   , cb=settingCallback, value= 1),
   Button((110, 60,100,120), bg='quit-ok', cb=quitCallback),
   Button((  0, 10,320, 35), bg='quit')]
]


# Assorted utility functions -----------------------------------------------

def setFxMode(n):
	global fxMode
	fxMode = n
	camera.image_effect = fxData[fxMode]
	buttons[4][5].setBg('fx-' + fxData[fxMode])

def saveSettings():
	try:
	  outfile = open('cam.pkl', 'wb')
	  # Use a dictionary (rather than pickling 'raw' values) so
	  # the number & order of things can change without breaking.
	  d = { 'fx'    : fxMode}
	  pickle.dump(d, outfile)
	  outfile.close()
	except:
	  pass

def loadSettings():
	try:
	  infile = open('cam.pkl', 'rb')
	  d      = pickle.load(infile)
	  infile.close()
	  if 'fx'    in d: setFxMode(   d['fx'])
	except:
	  pass

# Scan files in a directory, locating JPEGs with names matching the
# software's convention (IMG_XXXX.JPG), returning a tuple with the
# lowest and highest indices (or None if no matching files).
def imgRange(path):
	min = 9999
	max = 0
	try:
	  for file in os.listdir(path):
	    if fnmatch.fnmatch(file, 'IMG_[0-9][0-9][0-9][0-9].JPG'):
	      i = int(file[4:8])
	      if(i < min): min = i
	      if(i > max): max = i
	finally:
	  return None if min > max else (min, max)

# Busy indicator.  To use, run in separate thread, set global 'busy'
# to False when done.
def spinner():
	global busy, screenMode, screenModePrior

	buttons[screenMode][2].setBg('working')
	buttons[screenMode][2].draw(screen)
	pygame.display.update()

	busy = True
	n    = 0
	while busy is True:
	  buttons[screenMode][3].setBg('work-' + str(n))
	  buttons[screenMode][3].draw(screen)
	  pygame.display.update()
	  n = (n + 1) % 5
	  time.sleep(0.15)

	buttons[screenMode][2].setBg(None)
	buttons[screenMode][3].setBg(None)
	screenModePrior = -1 # Force refresh

def dodge(a, b, alpha):
    return min(int(a*255/(256-b*alpha)), 255)

def drawing(im1, blur=25, alpha=1.0):
	im3 = im1.convert("L")
	im2 = im3.copy()
	im2 = ImageOps.invert(im2)
	for i in range(blur):
		im2 = im2.filter(ImageFilter.BLUR)
	width, height = im1.size
	for x in range(width):
		for y in range(height):
			a = im3.getpixel((x, y))
			b = im2.getpixel((x, y))
			im3.putpixel((x, y), dodge(a, b, alpha))
	return im3

def takePicture():
	global busy, gid, loadIdx, saveIdx, scaled, uid, printer

	if not os.path.isdir(pathData):
	  try:
	    os.makedirs(pathData)
	    # Set new directory ownership to pi user, mode to 755
	    os.chown(pathData, uid, gid)
	    os.chmod(pathData,
	      stat.S_IRUSR | stat.S_IWUSR | stat.S_IXUSR |
	      stat.S_IRGRP | stat.S_IXGRP |
	      stat.S_IROTH | stat.S_IXOTH)
	  except OSError as e:
	    # errno = 2 if can't create folder
	    #print errno.errorcode[e.errno]
	    return

	saveIdx = 1

	# Scan for next available image slot
	while True:
		filename = pathData + '/IMG_' + '%04d' % saveIdx + '.JPG'
		if not os.path.isfile(filename): break
		saveIdx += 1
		if saveIdx > 9999: saveIdx = 0

	t = threading.Thread(target=spinner)


	scaled = None
	camera.resolution = sizeData[0]
	camera.crop       = sizeData[2]
	try:
		camera.capture(filename, use_video_port=False, format='jpeg',	    thumbnail=None)
		t.start()
		# Set image file ownership to pi user, mode to 644
		os.chmod(filename, stat.S_IRUSR | stat.S_IWUSR | stat.S_IRGRP | stat.S_IROTH)
		img    = pygame.image.load(filename)
		pilImg = PILImage.open(filename)
		wpercent = (700.0/float(pilImg.size[0]))
		hsize = int((float(pilImg.size[1])*float(wpercent)))
		pilImg = pilImg.resize((700,hsize), PILImage.ANTIALIAS).crop((0, 0, 700, 384)).transpose(PILImage.ROTATE_90).convert("L")
		#pilImg.save(filename, "JPEG")
		sharpness = ImageEnhance.Sharpness(pilImg)		
		pilImg = sharpness.enhance(3)

		brightness = ImageEnhance.Brightness(pilImg)
		pilImg = brightness.enhance(1.2)

		contrast = ImageEnhance.Contrast(pilImg)
		pilImg = contrast.enhance(2)

		pilImg.save(filename, "JPEG")
		scaled = pygame.transform.scale(img, sizeData[1])


	except Exception, e:
		traceback.print_exc(file=sys.stdout)

	finally:
		# Add error handling/indicator (disk full, etc.)
		camera.resolution = sizeData[1]
		camera.crop       = (0.0, 0.0, 1.0, 1.0)

	busy = False
	t.join()

	
	try:
		if scaled:
		  if scaled.get_height() < 240: # Letterbox
		    screen.fill(0)
		  screen.blit(scaled, ((320 - scaled.get_width() ) / 2, (240 - scaled.get_height()) / 2))
		  pygame.display.update()

		  printer.printImage(pilImg,True)
		  time.sleep(0.3)
		  printer.feed(2)
		  time.sleep(2.5)
		  loadIdx = saveIdx

	except Exception, e:
		traceback.print_exc(file=sys.stdout)


def showNextImage(direction):
	global busy, loadIdx

	t = threading.Thread(target=spinner)
	t.start()

	n = loadIdx
	while True:
	  n += direction
	  if(n > 9999): n = 0
	  elif(n < 0):  n = 9999
	  if os.path.exists(pathData+'/IMG_'+'%04d'%n+'.JPG'):
	    showImage(n)
	    break

	busy = False
	t.join()

def showImage(n):
	global busy, loadIdx, scaled, screenMode, screenModePrior, sizeMode

	t = threading.Thread(target=spinner)
	t.start()

	img      = pygame.image.load(pathData + '/IMG_' + '%04d' % n + '.JPG')
	scaled   = pygame.transform.scale(img, sizeData[1])
	loadIdx  = n

	busy = False
	t.join()

	screenMode      =  0 # Photo playback
	screenModePrior = -1 # Force screen refresh


# Initialization -----------------------------------------------------------
printer = Adafruit_Thermal("/dev/ttyAMA0", 19200, timeout=5)

# Init framebuffer/touchscreen environment variables
os.putenv('SDL_VIDEODRIVER', 'fbcon')
os.putenv('SDL_FBDEV'      , '/dev/fb1')
os.putenv('SDL_MOUSEDRV'   , 'TSLIB')
os.putenv('SDL_MOUSEDEV'   , '/dev/input/touchscreen')

# Get user & group IDs for file & folder creation
# (Want these to be 'pi' or other user, not root)
s = os.getenv("SUDO_UID")
uid = int(s) if s else os.getuid()
s = os.getenv("SUDO_GID")
gid = int(s) if s else os.getgid()

# Buffers for viewfinder data
rgb = bytearray(320 * 240 * 3)
yuv = bytearray(320 * 240 * 3 / 2)

# Init pygame and screen
pygame.init()
pygame.mouse.set_visible(False)
screen = pygame.display.set_mode((0,0), pygame.FULLSCREEN)

# Init camera and set up default values
camera            = picamera.PiCamera()
atexit.register(camera.close)
camera.resolution = sizeData[1]
#camera.crop       = sizeData[2]
camera.crop       = (0.0, 0.0, 1.0, 1.0)
# Leave raw format at default YUV, don't touch, don't set to RGB!

# Load all icons at startup.
for file in os.listdir(iconPath):
  if fnmatch.fnmatch(file, '*.png'):
    icons.append(Icon(file.split('.')[0]))

# Assign Icons to Buttons, now that they're loaded
for s in buttons:        # For each screenful of buttons...
  for b in s:            #  For each button on screen...
    for i in icons:      #   For each icon...
      if b.bg == i.name: #    Compare names; match?
        b.iconBg = i     #     Assign Icon to Button
        b.bg     = None  #     Name no longer used; allow garbage collection
      if b.fg == i.name:
        b.iconFg = i
        b.fg     = None

loadSettings() # Must come last; fiddles with Button/Icon states


# Main loop ----------------------------------------------------------------

while(True):

  # Process touchscreen input
  while True:
    for event in pygame.event.get():
      if(event.type is MOUSEBUTTONDOWN):
        pos = pygame.mouse.get_pos()
        for b in buttons[screenMode]:
          if b.selected(pos): break

    # If in viewfinder or settings modes, stop processing touchscreen
    # and refresh the display to show the live preview.  In other modes
    # (image playback, etc.), stop and refresh the screen only when
    # screenMode changes.
    if screenMode >= 3 or screenMode != screenModePrior: break

  # Refresh display
  if screenMode >= 3: # Viewfinder or settings modes
    stream = io.BytesIO() # Capture into in-memory stream
    camera.capture(stream, use_video_port=True, format='raw')
    stream.seek(0)
    stream.readinto(yuv)  # stream -> YUV buffer
    stream.close()
    yuv2rgb.convert(yuv, rgb, sizeData[1][0], sizeData[1][1])
    img = pygame.image.frombuffer(rgb[0:(sizeData[1][0] * sizeData[1][1] * 3)], sizeData[1], 'RGB')

  elif screenMode < 2: # Playback mode or delete confirmation
    img = scaled       # Show last-loaded image
  else:                # 'No Photos' mode
    img = None         # You get nothing, good day sir

  if img is None or img.get_height() < 240: # Letterbox, clear background
    screen.fill(0)
  
  if img:
    screen.blit(img,
      ((320 - img.get_width() ) / 2,
       (240 - img.get_height()) / 2))

  pygame.draw.rect(screen,(0,0,20), (0,176,320,64),0)


  # Overlay buttons on display and update
  for i,b in enumerate(buttons[screenMode]):
    b.draw(screen)

  pygame.display.update()

  screenModePrior = screenMode
