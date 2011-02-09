import sys
import os
from taintmode import *
from sanitize  import *

os.system = ssink(OSI)(os.system)
s_usermail = cleaner(OSI)(s_usermail)
s_file = cleaner(OSI)(s_file)

usermail = taint(sys.argv[1])
file = taint(sys.argv[2])
#usermail = s_usermail(usermail)
#file = s_file(file) 
cmd = 'mail -s "Requested file" ' 
      + usermail + ' < ' + file
os.system(cmd)
