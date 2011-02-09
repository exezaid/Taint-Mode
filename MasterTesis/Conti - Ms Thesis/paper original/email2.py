import sys
import os
from taintmode import untrusted, ssink, OSI

os.system = ssink(OSI)(os.system)

@untrusted
def get_datos(argumentos):
    return [argumentos[1], argumentos[2]]

usermail, filename = get_datos(sys.argv)

cmd = 'mail -s "Requested file" ' + usermail + ' < ' + filename
os.system(cmd)
