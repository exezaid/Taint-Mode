import sys
import os

usermail = sys.argv[1]
file = sys.argv[2]

cmd = 'mail -s "Requested file" ' 
      + usermail + ' < ' + file
os.system(cmd)



