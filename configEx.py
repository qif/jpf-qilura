import os
import subprocess
import glob

omega = 'symbolic.reliability.omegaPath=' + subprocess.Popen(['which', 'oc'], stdout=subprocess.PIPE).stdout.readline()
latte = 'symbolic.reliability.lattePath=' + subprocess.Popen(['which', 'count'], stdout=subprocess.PIPE).stdout.readline()

def editPath(conf):
	with open(conf,'r') as f:
		newlines = []
		for line in f.readlines():
			if 'omegaPath' in line:
				line = omega
			if 'lattePath' in line:
				line = latte
        		newlines.append(line)
	with open(conf, 'w') as f:
    		for line in newlines:
        		f.write(line)

curdir = os.getcwd()

array_conf = glob.glob(curdir + '/src/examples/*.jpf')

for conf in array_conf:
	editPath (conf)


