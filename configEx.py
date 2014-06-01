import os
import subprocess
import glob

oc = subprocess.Popen(['which', 'oc'], stdout=subprocess.PIPE).stdout.readline().rstrip()
latte = subprocess.Popen(['which', 'count'], stdout=subprocess.PIPE).stdout.readline().rstrip()

curdir = os.getcwd()

array_conf = glob.glob(curdir + '/src/examples/*.jpf')

for conf in array_conf:
	print conf
