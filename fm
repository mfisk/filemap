#!/usr/bin/env python
#
# FileMap - http://mfisk.github.com/filemap
#
# Public Domain License:
#
# This program was prepared by Los Alamos National Security, LLC at
# Los Alamos National Laboratory (LANL) under contract
# No. DE-AC52-06NA25396 with the U.S. Department of Energy (DOE). All
# rights in the program are reserved by the DOE and Los Alamos
# National Security, LLC.  Permission is granted to the public to copy
# and use this software without charge, provided that this Notice and
# any statement of authorship are reproduced on all copies.  Neither
# the U.S. Government nor LANS makes any warranty, express or implied,
# or assumes any liability or responsibility for the use of this
# software.
#
# Author: Mike Fisk <mfisk@lanl.gov>
#

# FileMap currently runs in python 2 or python 3, and with mixed versions between controller and remote nodes
from __future__ import absolute_import
from __future__ import print_function

import atexit
import base64
import bisect
import copy
import io
import errno
import fcntl
import glob
import grp
import gzip
import itertools
import math
import optparse
import os
import pipes
import pwd
import random
import re
import select
import shlex
import shutil
import signal
import socket
import stat
import string
import subprocess
import sys
import tempfile
import time
import traceback
import zlib

if int(sys.version[0]) > 2:
   RAWSTDIN = sys.stdin.buffer
   RAWSTDOUT = sys.stdout.buffer
   import pickle
   import configparser
   iteritems = dict.items
else:
   RAWSTDIN = sys.stdin
   RAWSTDOUT = sys.stdout
   import cPickle as pickle
   import ConfigParser as configparser
   iteritems = dict.iteritems

try:
   import hashlib # New for python 2.5
   sha = hashlib.sha1
except:
   import sha
   sha = sha.sha

# Globals
Verbose = 0
RegressionTest = False
Locations = None

ConfigApply = {
   "ssh": os.path.expanduser,
   "syncdir": os.path.expanduser,
   "rootdir": os.path.expanduser,
   "cowdir": os.path.expanduser,
   "python": os.path.expanduser,
   "fm": os.path.expanduser,
   "share": float,
   "cpusperjob": int,
   "processes": int,
   "dynamicload": float,
   "demand": int,
   "replication": int,
   "umask": int,
   "all2all_retries": int,
}

ConfigDefaults = {
   "ssh": "ssh -o GSSAPIDelegateCredentials=yes -o ConnectTimeout=5 -o StrictHostKeyChecking=no -Ax",
   "rsync": "rsync -tO",
   "share": "1",
   "syncdir": "/tmp/fmsync",
   "python": "python",
   "processes": "1000",
   "dynamicload": ".1",
   "inactive": False,
   "queuebyhost": False,
   "hostname": None,
   "cpusperjob": "1",
   "cowdir": "",
   "demand": "3",
   "replication": "1",
   "umask": "0002",
   "pathextras": "",
   "environ": None,
   "all2all_retries": "7",
}

def dictListAppend(map, key, value):
   if key not in map:
      map[key] = [value]
   else:
      map[key].append(value)

def printableHash(s):
   h = sha(s.encode('utf-8')).digest()
   h = base64.b64encode(h, b'+_')  # Normal b64 but / is _
   h = h.rstrip(b'\n\r =')
   return h.decode('utf-8')

Hostname = socket.gethostname().split('.')[0]
My_file_prefix = "_".join([Hostname, str(os.getpid())])

def isremote(hname):
   if not hname:
      return False

   hname = hname.split('.')[0]
   if Hostname == hname:
      return False
   else:
      return True

nonalphanumre = re.compile('[^a-zA-Z0-9\_\%\^\(\)\~\,\:\.\-]')

def escape(slist):
   """Take a list of strings and return a name usable as a filename."""

   (s, num) = nonalphanumre.subn(lambda m: "=%02X" % ord(m.group()), ' '.join(slist))
   s = s.replace('=20', '+')

   base = os.path.basename(s)

   # Make sure it's not too long to be a filename
   if len(base) > 220:
      # Use a hash of the remainder 
      base = base[:220] + printableHash(base[220:])
      s = os.path.join(os.path.dirname(s), base)

   return s

quoprire = re.compile('=([0-9a-fA-F]{2})')

def lsUnescapeChr(m):
   c = m.group(1).decode('hex')
   if c == '/':
      c = '\\/'
   if c == '\\':
      c = '\\\\'
   return c

def tabulate(lst, width, ncols=None):
   if not lst:
      return None
   smallest = min([len(l) for l in lst])

   if ncols == None:
      # Initial case, start with each column being as wide as narrowest element
      ncols = int((width+2) / (smallest+2))
      ncols = max(1, ncols)

   # See if we can build a table with this many columns
   minwidths = [smallest] * ncols
   nrows = int(math.ceil(len(lst)*1.0 / ncols))
   for c in range(0, ncols):
      colwidth = minwidths[c]
      for r in range(0, nrows):
         i = c * nrows + r
         if i > (len(lst)-1): break
         lel = len(lst[c*nrows + r])
         if lel > colwidth:
            colwidth = lel
            minwidths[c] = lel
 
            # But expanding this one may mean we can have fewer columns
            startcol = c
            if ncols > 1 and (sum(minwidths) + 2*len(minwidths)) > (width+2):
               return tabulate(lst, width, ncols-1)

   # If we got here, then the sizes fit!
   for r in range(0, nrows):
      line = []
      for c in range(0, ncols):
         i = c*nrows + r
         if i > (len(lst)-1):
            break
         line.append("%-*s" % (minwidths[c], lst[i]))
      line =  '  '.join(line)
      line = line.rstrip()
      print(line)

def rewriteList(lst, f):
   """Apply a function to each element in a list.
      If the function returns None, use the original item.
      If the function returns a Tuple, replace with _contents_ of tuple. 
      Else replace the element with what the function returns.
   """
   ret = []
   for l in lst:
      out = f(l)
      if out == None:
         ret.append(l)
      elif type(out) == type(()):
         for i in out:
            ret.append(i)
      else:
         ret.append(out)
   return ret

if RegressionTest:
   def rewriteTest(item):
      if item == 1: return 2
      if item == 2: return 'a','b'
      if item == 3: return ['a', 'b']
      if item == 4: return ()
      return

   assert( rewriteList([1,2,3,4,5], rewriteTest1) == [2, 'a', 'b', ['a', 'b'], 5])

  
def collapseIntervals(lst):
   """Take list of (start,end) interval tuples and return a similar list with all overlapping intervals combined."""
   intervals = []
   for (sstart,send) in lst:
      found = False
      for i in range(0, len(intervals)):
         (start,end) = intervals[i]
         if (sstart <= end and send > end) or (send >= start and sstart < start):
            # Expand interval (note this may make this interval overlap with one of the ones already in the list)
            start=min(start,sstart)
            end=max(end,send)
            #print >>sys.stderr, "Changing", intervals[i], "to", (start,end)
            intervals[i] = (start,end)
            found = True
            break
         elif send <= end and start >=start:
            # Already encompassed
            found = True
      if not found:
         # Add new interval to list
         intervals.append((sstart,send))
         #print >>sys.stderr, "Adding", (sstart,send), intervals

   # Repeat until no more merges left
   while lst != intervals:
      lst = intervals
      intervals = collapseIntervals(lst)

   return intervals

if RegressionTest:
   assert(collapseIntervals([(1,3), (2,4), (2,3), (1,4), (0,2), (5,6), (4,4.5)]) == [(0,4.5), (5,6)])

def mkdirexist(path):
   try:
      os.makedirs(path)
   except OSError as e:
      if e.errno == errno.EEXIST:
         pass
      else:
         raise

def coallesce(outputs, labels):
   """Take a list of multi-line strings and an equally long list of labels and return a string summarizing which labels had what output."""
   assert(len(outputs) == len(labels))
   sameas = {}
   result = ""

   for i in range(0, len(outputs)):
      if outputs[i]:
         header = [labels[i]]
         for j in range(i+1, len(outputs)):
            if outputs[j] and outputs[i].getvalue() == outputs[j].getvalue():
               header.append(labels[j])
               outputs[j] = None

         header.sort(key=numcmptokenize)
         header = ','.join(header)
         header += ": "
         
         for line in outputs[i]:
            result += header + line.decode()

   return result
 
def multiglob(globs):
   """Take a list of globs and return a list of all of the files that match any of those globs."""

   assert(type(globs) == type([]))
   ret = []
   for g in globs:
      ret += glob.glob(g)
   return ret


num_re = re.compile('^(([\D]+)|(\d+))')

def numcmptokenize(x):
   xlist = []

   while x:
      xn = num_re.match(x)
      if not xn:
         return x
      xlen = len(xn.group(0))
      token = x[:xlen]
      try:
         token = int(token)
      except:
         pass
      xlist.append(token)
      x = x[xlen:]

   return xlist

def statOverlap(joba, jobb):
   """Return true iff duration of joba does not overlap with duration of jobb."""

   if jobb['start'] > joba['finish'] or joba['start'] > jobb['finish']:
      return False
   return True

def makeVnodes(nodes):
   # We may have multiple jobs at a time per node (e.g. SMP nodes), so 
   # treat those as multiple nodes.  Since we don't have an explicit thread id, 
   # just assign them arbitrarily in a non-overlapping way
   newnodes = {}
   for nodename in nodes.keys():
      vnodes = []
      nodes[nodename].sort(lambda a,b: cmp(a['start'], b['start']))
      for job in nodes[nodename]:
         found = False
         for vnode in vnodes:
            if not statOverlap(job, vnode[-1]):
               # Does not overlap with last job in this vnode, so append it here
               vnode.append(job)
               found = True
               break
         if not found:
            # Make new node
            vnodes.append([job])
         #print "now", vnodes

      #print "Replacing", nodename, "with", len(vnodes)
      for i in range(0, len(vnodes)):
         newnodes[nodename + ";" + str(i)] = vnodes[i]
         #print nodes.keys()
   
   return newnodes
   
def plot(inputfile, pngfile, options):
   import matplotlib.figure
   import matplotlib.collections
   import matplotlib.backends.backend_agg

   stats = pickle.load(inputfile)
   inputfile.close()

   # Load all stats and keep track of min and max inputsizes along the way
   nodes = {}
   jobs = {}
   cmds = {}
   copies = {}
   minsize = None
   mintime = None
   maxsize = 0
   maxtime = 0
   totalsize = 0
   nodename = 'nodename'
   if options.group_host:
      nodename = 'hostname'
     
   stats.sort(lambda a,b: cmp(a['start'], b['start']))

   for s in stats:
      s['finish'] = s['timestamp']
      if not nodes.get(s[nodename]):
         nodes[s[nodename]] = []
      nodes[s[nodename]].append(s)

      if minsize == None:
         minsize = s['inputsize']
      else:
         minsize = min(minsize, s['inputsize'])

      maxsize = max(maxsize, s['inputsize'])

      if mintime == None:
         mintime = s['start']
      else:
         mintime = min(mintime, s['start'])

      maxtime = max(maxtime, s['finish'])
      totalsize += s['inputsize']

      jobname = s['jobname']

      cmds[jobname] = jobname[:4] + ': ' + ' '.join(s['cmd'])

      # Keep track of earliest start time
      if jobname in jobs:
         jobs[jobname] = min(jobs[jobname], s['start'])
      else:
         jobs[jobname] = s['start']

      # Count duplicate processing of a file and assign each element a serial number (in order of start, not completion)
      copies.setdefault(s['statusfile'], 0)
      copies[s['statusfile']] += 1
      if options.redundant and copies[s['statusfile']] > 1:
         print(s['statusfile'], 'redundant', s['start'], s['finish'], s['nodename'])
         
      s['copies'] = copies[s['statusfile']]

   # Reduce to overlapping windows
   intervals = [(i['start'], i['finish']) for i in stats]
   intervals = collapseIntervals(intervals)
   active = sum([i[1] - i[0] for i in intervals])
   gaps = []
   if intervals:
      prev = intervals.pop(0)
      for i in intervals:
         # If more than 10% of the total duration is skipped here, then edit it out
         if i[0] - prev[1] >  0.1*(active):
            # A noticeable gap occurs between these
            gaps.append((prev[1], i[0]))
            #print >>sys.stderr, "Gap between", prev[1], i[0]
         prev = i

   nodes = makeVnodes(nodes)

   if Verbose > 1:
      print("Data spans", seconds2human(maxtime-mintime), "with", seconds2human(active), "active", file=sys.stderr)
      print("Packed into", len(nodes), "timelines", file=sys.stderr)

   # invert the jobs->start map
   start = {}
   for j in jobs:
      start[jobs[j]] = j  
   starts = list(start.keys())
   starts.sort()

   # make jobs a list sorted in order of start time
   jobs = [start[j] for j in starts]

   if Verbose > 2:
      print("Assigning colors to", len(jobs), "jobs", file=sys.stderr)
   colormap = ['blue','red','green','black', 'magenta', 'purple', 'cyan', 'yellow']
   color = {}
   fakebars = []
   legends = []
   for j in jobs:
      color[j] = jobs.index(j)
      color[j] = colormap[color[j] % len(colormap)]
      if Verbose > 2:
         print("Job %s %s" % (color[j],j), file=sys.stderr)

      # broken_bars don't generate a legend, so make bars for legend manually
      fakebars.append(matplotlib.patches.Rectangle((0, 1), 1, 1, fc=color[j]))
      legends.append(cmds[j])

   fig = matplotlib.figure.Figure(figsize=(8,10.5))
   ax = fig.add_subplot(111)
   ax.set_autoscale_on(True)
 
   # Add the legend 
   fontsize = 800. / max([len(j) for j in jobs]) #Scale for line width
   fontsize = min(fontsize, 30. / len(jobs)) # Scale for number of lines
   fontsize = min(10, fontsize) # No bigger than 10pt
   fontsize = max(1, fontsize) # No smaller than 1pt
  
   try:
      ax.legend(fakebars, legends, bbox_to_anchor=(0,1,1,1), frameon=False, loc=8, prop={'size': fontsize}, title="%s processed" % (bytecount2str(totalsize)))
   except:
      ax.legend(fakebars, legends, bbox_to_anchor=(0,1,1,1), loc=8, prop={'size': fontsize}, title="%s processed" % (bytecount2str(totalsize)))
         
   nodenames = list(nodes.keys())
   nodenames.sort(cmp=numcmp)

   # Build map of nodenames to y coordinates
   nodes2y = {}
   i = 0
   for n in nodenames:
      nodes2y[n] = i
      i += 1

   lines = []
   if not maxsize:
      maxsize = 0
   else:
      maxsize = math.log(maxsize)

   if not minsize:
      minsize = 0
   else:
      minsize = math.log(minsize)

   for node in nodenames:
      y = nodes2y[node]

      if Verbose > 2:
         print("Plotting line", node, "with", len(nodes[node]), "elements", file=sys.stderr)
      for s in nodes[node]:

         finish = s['finish']
         start = s['start']

         # Size is a log-scale number between 0 and 1 where 0 is the minimum size seen in this run and 1 is the max size seen in this run
         insize = s['inputsize']
         if insize:
            insize = math.log(insize)
         else:
            insize = 0
         size = (insize-minsize)/(maxsize-minsize)
         size = size * 0.7 + 0.3 #Makem min size be 30%
   
         # CPU is % of wallclock time in user or system CPU time
         if s['time'] == 0:
            cpu = 1
         else:
            cpu = (s['utime'] + s['stime']) / s['time']

         # Adjust for time gaps
         delta = 0
         for g in gaps:
            if g[1] <= start:
               delta += g[1] - g[0]   
         lw = min(1, s['copies'] - 1)  # Outline duplicates more and more 
         ax.broken_barh([(start-mintime-delta, finish-start)], [y-0.5*size,size], alpha=0.3+cpu, lw=lw, facecolor=color[s['jobname']])

   ax.autoscale_view()

   # Minor (gap) labels  
   xlabels = []
   xticks = []
   delta = 0
   for g in gaps:
      xticks.append(g[0] - delta - mintime)
      xlabels.append(seconds2human(g[1]-g[0]) + " idle")
      delta += g[1] - g[0]
   ax.set_xticks(xticks, minor=True)
   ax.set_xticklabels(xlabels, minor=True, rotation=30, ha='right', size=8)
   
   # Major (min/max) labels
   t = maxtime-mintime-delta
   ax.set_xticks([0, t])
   ax.set_xticklabels([0, seconds2human(t)])#, rotation=30, ha='right')

   ax.set_xlim(xmin=0, xmax=t)

   majorlabels = []
   majorlocs = []
   minorlabels = []
   minorlocs = []
   majors = []
   for n in nodenames:
      if n.endswith(";0"):
         name = n[:-2]
         if "." in n:
            major,minor = name.split(".", 1)
         else:
            major = name
            minor = None

         if major in majors:
            if minor:
               minorlabels.append("." + minor)
               minorlocs.append(nodes2y[n])
            else:
               minorlabels.append(name)
               minorlocs.append(nodes2y[n])

         else:
            majors.append(major)
            majorlabels.append(name)
            majorlocs.append(nodes2y[n])

   ax.set_yticks(majorlocs)
   ax.set_yticklabels(majorlabels, size=6)

   if len(majorlocs) < 50:
      ax.set_yticks(minorlocs, minor=True)
      ax.set_yticklabels(minorlabels, size=4, minor=True)
      
   ax.set_ylim(ymin=-2, ymax=len(nodenames)+2)
   #ax.set_title("%s processed" % (bytecount2str(totalsize)))

   canvas = matplotlib.backends.backend_agg.FigureCanvasAgg(fig)
   canvas.print_figure(pngfile, antialias=False, dpi=600)

   return None

def bytecount2str(n):
   unit = 'B'
   units = ['kB', 'MB', 'GB', 'TB', 'PB']
   while n >= 1000 and len(units):
      n /= 1000.0
      unit = units.pop(0)
   return ("%3.1f" % n) + ' ' + unit

def seconds2human(s):
   if s < 60:
     return "%.0fs" % s
   if s < 3600:
     return "%.0fm" % (s/60.)
   if s < 86400:
     return "%.1fh" % (s/3600.)
   if s < 864000:
     return "%.1fd" % (s/86400.)
   else:
     return "%.1fwk" % (s/604800.)
   
class MethodOptionParser(optparse.OptionParser):
   """OptionParser to be instantiated by dispatch methods of a class.  Sets %prog to be the calling function name and epilog to be the doc string for that function.  Also prints options in usage string more like man conventions instead of just [options]."""

   def __init__(self, *args, **kwargs):
      if 'epilog' not in kwargs:
         caller = sys._getframe(1)
         pmethod = caller.f_code.co_name
         pself = caller.f_locals['self']
         method = pself.__class__.__dict__[pmethod]
         kwargs['prog'] = pmethod
         self.Epilog = method.__doc__ or ""

      if 'fixed' in kwargs:
         self.fixed = kwargs['fixed']
         del kwargs['fixed']
      else:
         self.fixed = None

      self.numrequired = 0
      if self.fixed:
         for i in self.fixed:
            if i[0] != "[":
               self.numrequired += 1 

      optparse.OptionParser.__init__(self, *args, **kwargs)
      self.disable_interspersed_args()

   def parse_args(self, args):
      (options, args) = optparse.OptionParser.parse_args(self, args)
      if len(args) < self.numrequired:
         print("Required argument(s) missing", file=sys.stderr)
         self.print_help()
         sys.exit(1)
      return (options, args)

   def get_usage(self):
      if self.fixed != None:
         flags = []
         options = ''
         for o in self.option_list:
            if o.action == 'store_true':
               flags += o._short_opts[0].lstrip('-')
            elif o.action == 'help':
               pass
            else:
               opts_tmp_fmts = []
               opts_tmp_vals = []
               if o._short_opts:
                  opts_tmp_fmts.append("%s")
                  opts_tmp_vals.append(o._short_opts[0])
               if o._long_opts:
                  opts_tmp_fmts.append("%s")
                  opts_tmp_vals.append(o._long_opts[0].lstrip('-').upper())
                  
               options += ("[" + " ".join(opts_tmp_fmts) + "]") % tuple(opts_tmp_vals)
               if o.action == 'append':
                  options += '...'
               
               options += ' '

         flags = ''.join(flags)
         if flags:
            options += "[-" + flags + "] "
         
         self.usage = "%prog " + options + ' '.join(self.fixed)

      return optparse.OptionParser.get_usage(self)

   def print_help(self):
      r = optparse.OptionParser.print_help(self)
      
      # For python < 2.5, we have to print our own epilog 
      print()
      print(self.Epilog)
      return r

class SmartDict(dict):
      def __getattr__(self, name):
         try:
            return self[name]
         except KeyError as e:
            raise AttributeError(e)
      def __setattr__(self, name, value):
         self[name] = value

def tryrmtree(dir):
   try:
      shutil.rmtree(dir)
   except:
      pass

def mkstemp(prefix, suffix):
   dir = "/%s/fm-%s/%d" % (os.environ.get('TMPDIR', '/tmp'), os.environ.get('USER', 'none'), os.getpid())
   mkdirexist(dir)
   atexit.register(tryrmtree, dir)
   return tempfile.mkstemp(prefix=prefix, dir=dir, suffix=suffix)

def mkdtemp(prefix):
   dir = "/%s/fm-%s/%d" % (os.environ.get('TMPDIR', '/tmp'), os.environ.get('USER', 'none'), os.getpid())
   mkdirexist(dir)
   atexit.register(tryrmtree, dir)
   return tempfile.mkdtemp(prefix=prefix, dir=dir)

class FmLocations:
   def __init__(self, copyFrom=None, locs={}, slave=False):
      self.procs = None
      self.locker = None
      self.cleanup = None
      self.cached_dstnodes = {}

      if copyFrom and not slave:
         assert(locs)
         self.config = copy.deepcopy(copyFrom.config)
         self.config.locs = locs
         self.procs = copyFrom.procs
         self.locker = copyFrom.locker

         self.this = copyFrom.this

      elif slave:
         assert(copyFrom)
         self.config = copyFrom.config
         self.thisis(slave)

         # Keep a copy of the config around so our children (like redistribute) can reference it
         fd, name = mkstemp(prefix="locations", suffix=".pickle")
         self.cleanup = name
         #print("locations is", name, file=sys.stderr)
         os.environ['FMCONFIG'] = name
         fh = os.fdopen(fd, 'wb')
         fh.write(pickle.dumps(self.config, protocol=2))
         fh.close()
      else:
         self.config = SmartDict() # like a named tuple but for older python
         self.config.locs = {}

         filename = os.environ.get('FMCONFIG')
         #print >>sys.stderr, "Env filename is", filename
         if not filename:
            if os.path.isfile("filemap.conf"):
               filename = "filemap.conf"
            elif os.path.isfile(os.path.expanduser("~/.filemap.conf")):
               filename = os.path.expanduser("~/.filemap.conf")
            else:
               filename = "/etc/filemap.conf"

            os.environ['FMCONFIG'] = filename

         try:
            fh = open(filename)
         except:
            raise Exception("Unable to locate config file.  Set FMCONFIG or place filemap.conf in . or /etc")

         if filename.endswith('.pickle'):
            self.config = pickle.load(fh)
         else:
            self.parseConfigFile(fh)

         #self.thisis('global')

      if self.this.pathextras:
         os.environ['PATH'] += ":" + self.this.pathextras

      if self.this.environ:
         for pair in self.this.environ.split():
            k,v = pair.split('=')
            os.environ[k] = v

      if self.this.umask:
         os.umask(self.this.umask)

      if not self.locker:
         self.locker = self.getSynchronizer()

      if not self.procs:
         self.procs = Procs()

   def parseConfigFile(self, fh):
      """Populate self.config from config file."""

      # Read from file
      self.configparser = configparser.ConfigParser()

      #print >>sys.stderr, "Reading config", filename, self.configparser.sections()
      self.configparser.readfp(fh)
  
      self.config.slurmfe = self.config_get("global", "slurmfe", None)
      if self.config.slurmfe == "localhost":
         self.config.slurmfe = "sh -c"

      # Unless we were passed an explicit list of locations, grab all
      # from the config file.
      if not self.config.locs:
         nl = self._getSlurmNodes(self)
 
         for s in self.configparser.sections():
            if s == "global":
               continue
            r = self._expandList(s)
            for (vals,name) in r:
               self.parseLocation(s, name=name, listvalues=vals)

      # Use global config values by default (thisis() can override later)
      self.parseLocation("global")

      # Once all config files settings are imported, prep the location for use (apply defaults, etc.)
      for l in self.config.locs.values():
         self.prepLocation(l)

         if nl:
            # Check SLURM_NODELIST to make sure we've been allocated this node
            if l.hostname not in nl:
               l.inactive = True
               #print "Marking", l.name, "inactive per SLURM", l.hostname, nl
 
      # Also prep the global section
      self.prepLocation(self.this)

   def _getSlurmNodes(self, alloc=True):
      nl = os.environ.get("SLURM_NODELIST")
      if not nl and not self.config.slurmfe:
         # Must not be running under SLURM
         return None

      if not nl:
         nl = subprocess.Popen(self.config.slurmfe.split() + ["squeue -t RUNNING -u $USER -o %i/%j/%N"], stdout=subprocess.PIPE, stdin=None)
         for line in nl.stdout:
             line = line.strip()
             (id,name,nl) = line.split('/')
             #print >> sys.stderr, "SLURM jobid", id, name, nl
             if name != "FM":
                nl = None
                continue
         
             os.environ["SLURM_NODELIST"] = nl
             os.environ["SLURM_JOBID"] = str(id)
             #print >> sys.stderr, "SLURM jobid", id, nl

             break  

         if not nl:
             if alloc:
                if Verbose > 0: print("Starting new FM job in SLURM", file=sys.stderr)
                subprocess.Popen(self.config.slurmfe.split() + ["salloc -k -J FM --nodes 1-9999 --overcommit --share --ntasks-per-node 2 --no-shell"], stdout=sys.stdout, stderr=sys.stderr, stdin=None).wait()
                return self._getSlurmNodes(alloc=False)
             else:
                print("Unable to find or start FM job found in SLURM", file=sys.stderr)
                sys.exit(2)

      assert(nl)

      # Check SLURM_NODELIST to make sure we've been allocated this node
      nl = self._expandList(nl)
      if Verbose > 0: print("Active SLURM nodes: ", nl, file=sys.stderr)
      nl = [i[1] for i in nl]
      return nl

   def __del__(self):
      if self.cleanup:
         os.unlink(self.cleanup)
         self.cleanup = None

   def _expandList(self, liststr, values=[]):
      """Returns a list of tuples where each tuple contains a list of 0 or more interval values and the resulting string from those values."""

      #Support () or [] syntax for SLURM or ConfigParser cases
      if not hasattr(self, 'range_fe'):
         self.range_re = re.compile("([^\(\[]*)[\(\[]([^\)\]]*)[\)\]](.*)$")

      r = self.range_re.match(liststr)
      if not r:
         return [(values, liststr)]
      prefix = r.group(1)
      lst = r.group(2)
      expanded = []
      suffix = r.group(3)
      first = None
      for interval in lst.split(","):
         if "-" in interval:
            (min,max) = interval.split("-")
            expanded += list(range(int(min), int(max)+1))
            if not first: first = min
         else:
            #singleton
            try:
               node = int(interval)
            except:
               node = interval
            expanded.append(node)
            if not first: first = interval

      #print >>sys.stderr, 'Expanding using %s as template' % first
      # Recursively try expanding each result (which may have a second list in it) and flatten the resulting lists
      ret = []
      for i in expanded:
         # It may be padded with leading zeros, the following will preserve that formatting:
         # First is the first example node number string.
         ret += self._expandList(prefix + str(first)[:-len(str(i))] + str(i) + suffix, values+[i])
          
      return ret

   def parseLocation(self, stanza, name=None, listvalues=[]):
      if name:
         nodename = str(name)
      else:
         nodename = str(stanza)

      # Reuse (add attributes to) existing Location if we already saw this nodename
      l = self.config.locs.get(nodename)
      if not l:
         l = FmLocation()
         if stanza != "global":
            self.config.locs[nodename] = l
         else:
            self.this = l # Assume by default that we're the head node and use global defaults

         l.name = nodename
         l.config = {}
         l.listvalues = listvalues
      elif not l.listvalues:
         l.listvalues = listvalues
      #elif [str(i) for i in l.listvalues] != [str(i) for i in listvalues]:
         #print >>sys.stderr, "Error: conflicting range information for node", nodename, l.listvalues, listvalues

      # Import all configparser settings into a dictionary
      for opt,val in self.configparser.items(stanza, raw=True):
         l[opt] = val

   def prepLocation(self, l):
      # Inherit all global defaults if not over-ridden
      for k,v in self.configparser.items("global", raw=True):
         if k not in l:
            l[k] = v

      # Inherit all hard-coded defaults if not over-ridden
      for k,v in ConfigDefaults.items():
         if k not in l:
            l[k] = v

      # Apply conversion/expansion functions
      for k,f in ConfigApply.items():
         if k in l:
            l[k] = f(l[k])

      l.sshcmd = shlex.split(l.ssh, comments=True)
      l.rsynccmd = shlex.split(l.rsync, comments=True)
      l.rsynccmd[0] = os.path.expanduser(l.rsynccmd[0])

      if l.name != "global":
            if l.values:
               if l.hostname:
                  #if '%' not in l.hostname:
                     #print >>sys.stderr, "Warning %s does not reference given instance %s" % (l.hostname, str(l.values))
                  try:
                     l.hostname = l.hostname.format(*l.listvalues)
                  except:
                     print("Error formatting", l.hostname, "with", l.listvalues, file=sys.stderr)
                     raise

               assert(l.rootdir)
               l.rootdir = l.rootdir.format(*l.listvalues)
            
            l.jobdir = l.rootdir + "/jobs"
            if l.queuebyhost:
               l.qname = l.hostname
            else:
               l.qname = l.name
   
            if 'fm' not in l:
               l.fm = l.rootdir + "/sys/fm"

            l.fmcmd = [l.python, l.fm]
            
   
   def config_get(self, section, key, defval=None, raw=False, merge=False, expanduser=False):
      if self.configparser.has_option(section, key):
         val = self.configparser.get(section, key, raw=raw)
      elif merge:
         # Use previous value
         pass
      else:
         if self.configparser.has_option("global", key):
            val = self.configparser.get("global", key, raw=raw)
         else:
            val = defval

      if expanduser and val:
         val = os.path.expanduser(val)

      return val

   def thisis(self, nodename):
      self.thisname = nodename
      if nodename == "global":
         self.this = self.config.locs['global']
      else:
         self.this = self.config.locs[nodename]

      self.locker = self.getSynchronizer()

   def getSynchronizer(self):
      if self.this.syncdir.startswith("redis:"):
          return RedisSynchronizer(self)
      else:
          return FileSynchronizer(self)

   def pickHosts(self):
      """Return a subset of locations containing only one location per hostname"""
      hosts = set()
      newlocs = {}
      for l in self.config.locs.values():
         if l.inactive or l.hostname in hosts:
            continue
         else:
            newlocs[l.name] = l
            hosts.add(l.hostname)
 
      newlocs = FmLocations(copyFrom=self, locs=newlocs)
      newlocs.this = self.this
      return newlocs
   
   def nodes(self, seed=None):
      """Generate a list of pseudo-random locations.  
      Specify a seed to get deterministic results (e.g. for a given extension 
      number, file name, path, etc).  Generate a list of node names."""

      # This implementation uses a Chord-like structure where nodes map to points on a ring.
      # The seed determines a point of interest on the ring.
      # Yield the nodes closest to that point (but after the point, for implementation simpicity)
 
      # This Chord approach allows the map of seed->nodes to be fairly stable as nodes are added or deleted

      # Build the node points for the Chord algorithm used by nodes()
      if 'chord' not in self.config:
          #print >>sys.stderr, "Generating chord assignments"
          candidates = list(self.config.locs.keys())
          mapping = {}
          for node in candidates:
              point = sha(node.encode('utf-8'))
              # For small numbers of nodes, we need multiple points per node in order to have any stability
              for _ in range(int(10 * self.config.locs[node].share)):
                  mapping[point.hexdigest()] = node
                  # Use a hash feedback loop to generate pseudo-random list of additional points
                  point = sha(point.digest() + node.encode('utf-8'))
   
          points = list(mapping.keys())
          points.sort()
          self.config.chord = mapping
          self.config.chord_points = points

      #print >>sys.stderr, "Getting chord for this"

      if not seed:
          seed = str(random.random())

      #print >>sys.stderr, self.config
      # Add point to set
      seed_point = sha(seed.encode('utf-8')).hexdigest()

      # Construct generator of points after seed_point 

      # Bisect the sequence
      point = bisect.bisect_left(self.config.chord_points, seed_point)
     
      # Build a generator of indices 
      indexes = itertools.chain(range(point, len(self.config.chord_points)), range(0, point))

      # Turn into a generator of points
      candidate_points = (self.config.chord_points[i] for i in indexes)

      #print >>sys.stderr, "generating chord"
      # Generate nodes without duplicates 
      used_candidates = set()
      for point in candidate_points:
          node = self.config.chord[point]
          if node not in used_candidates:
              used_candidates.add(node)
              yield node

   def pickn(self, seed=None, n=None):
      """Pick some pseudo-random locations.  The number of locations
      chosen is based on the replication factor in the config.
      Specify a seed to get deterministic results (e.g. for a given
      extension number.)  The return value is the list of node names."""

      # Try to yield the right $n$ for this seed and if none of those are active, the next replicate after that
      foundactive = False

      if not n:
         n = self.this.replication

      nodes = self.nodes(seed=seed)

      i = 0
      foundactive = 0
      for l in nodes:
         i += 1
         if foundactive > n:
            # Stop if we've examined $n$ and at least 1 was active
            break
         if not self.config.locs[l].inactive:
            foundactive += 1
            yield l

      if i < n:
         print("Cannot pick %d locations" % (n), file=sys.stderr)

   def pick(self, n=None, seed=None):
      """Return a new FmLocations instance that uses a subset of the
locations of this instance."""

      used = self.pickn(seed, n=n)

      assert(used)

      useddict = {}
      for u in used:
         useddict[u] = self.config.locs[u]

      return FmLocations(copyFrom=self, locs=useddict)
        
   def forAllLocal(self, cmd):
      """Same ase forAll(), but CMD will be run as arguments to "fm _local"."""
      if Verbose:
         verbose = "-" + "v" * Verbose
         lcmd = ["fm", verbose, "_local", "-n", "%(NODE)"] 
      else:
         lcmd = ["fm", "_local", "-n", "%(NODE)"] 

      inputs = {'cmd': cmd, 'config': self.config}

      return self.forAll(lcmd, subst=True, stdinstr=zlib.compress(pickle.dumps(inputs, protocol=2)), tag=' '.join(cmd))

   def forAll(self, Cmdv, src=[], dst=[], absolute=False, subst=False, trailer=None, glob=True, stdinstr=None, call=False, tag=None, quote=True):
      if src and type(src) != type([]):
         src = [src]
      if dst and type(dst) != type([]):
         dst = [dst]

      if not tag:
         tag = ' '.join(Cmdv + src + dst)

      if stdinstr:
         stdin = subprocess.PIPE

      for loc in self.config.locs.values():
         if loc.inactive:
            continue

         if subst:
            cmd = loc.subst(Cmdv)
            src = loc.subst(src)
         else:
            cmd = list(Cmdv)

         if absolute:
            s = list(src)
            d = list(dst)
         else:
            s = [loc.rootdir + "/" + f for f in src]
            d = [loc.rootdir + "/" + f for f in dst]

         if cmd[0] == "fm":
            cmd = loc.fmcmd + cmd[1:]

         if isremote(loc.hostname):
            if quote and "SLURM_JOBID" not in os.environ:
               # The remote sshd/shell will expand globs (unless it's SLURM's srun), so quote all the individual args
               s = ["'" + i + "'" for i in s]
               d = ["'" + i + "'" for i in d]

            filestr = ' '.join(s+d)
            if "SLURM_JOBID" in os.environ and not quote and ('*' in filestr or '?' in filestr):
               # Assume srun.  Srun doesn't expand globs or run a shell automatically, so we have to explicitly run /bin/sh
               cmd = loc.sshcmd + [loc.hostname, "sh", "-c", subprocess.list2cmdline(cmd + s + d)]
            else:
               cmd = loc.sshcmd + [loc.hostname] + cmd + s + d

         else:
            if s and glob:
               #time.sleep(random.random())  #RHEL5 + thumper glob issues
               s = multiglob(s)
               if not s:
                  continue

            if d and glob:
               d = multiglob(d)
               if not d:
                  continue

            cmd += s + d 
            
         if trailer:
            cmd += trailer

         self.procs.Popen(cmd, call=call, stdinstr=stdinstr, queue=loc.qname, tag=tag)


      return self.procs

   def expanddir(self, path):
            items = [] 
            for root,dirs,files in os.walk(path):
               for f in files:
                  fp = os.path.join(root, f)
                  items.append(fp)
            return items

   def put(self, srclist, dst, relativeroot=False, procs=None, pickn=False, hashbasename=False, serialize=False, remove=False):
      # We will glob this ourselves since we implicitly expand directories to the next level and, in the case of hashbasename, have to get the final filenames rather than globs in order to know where to put them.
      if not procs:
         procs = self.procs

      relative = {}

      # Pull out any directories we have to recurse.
      # Imagine a list like the following:
      #   a   (a,)
      #   /b/ (/b/c,b)
      #       (b/c/d,b/c)
      #   /e  (/e,)
      #   /f/ (/f/g,f)
      #       (/f/h,f)
      #   i/  (i/j,i)
      #       (i/k,i
      # We can only do this with fully qualified paths
      # Luckily, we use rsync which allows us to use "/./" elements to show which part of the path to preserve on the other side

      # When "relativeroot" is true, we're copying between nodes within the virtual filesystem and want to preserve paths
      if relativeroot:
         assert(dst == "/")
         # An intervening /./ in the path is how we denote the leading part that shouldn't be duplicated on the destination
         srcs = [self.this.rootdir + "/./" + s for s in srclist]
      else:
         srcs = []
         for s in srclist:
            s = s.rstrip('/') 
            dirname = os.path.dirname(s) or '.'
            s = dirname + '/./' + os.path.basename(s)
            srcs.append(s)
            #print("adding", s, file=sys.stderr)

      srcs = multiglob(srcs)
      if not srcs:
         print("No such file:", srclist, file=sys.stderr)
         return procs

      srcfiles = []
      for a in srcs:
         # Convert directory arguments to lists of files so we can assign them to the proper nodes
         if os.path.isdir(a):
            srcfiles += self.expanddir(a)
         else:
            srcfiles.append(a)

      tag = "put %s %s" % (srclist, dst)
      redundants = self.pickput(srcfiles, dst, procs, tag, pickn, hashbasename, serialize, remove, relativeroot)

      if remove and redundants:
         errors, results = procs.collect()
         # If no errors, then remove redundants
         if results and not errors:
            if Verbose > 1:
               print("Removing %d of %d: %s" % (len(redundants), len(srcs), list(redundants)), file=sys.stderr)
            for r in redundants:
               if os.path.isdir(r):
                  shutil.rmtree(r)
               else:
                  os.unlink(r)

      return procs

   def pickput(self, srcs, dst, procs, tag, pickn, hashbasename, serialize, remove, relativeroot):
      nodesrcs = {}
      relative = None
      for s in srcs:
         if hashbasename:
            seed = os.path.basename(s)
         elif "/./" in s:
            # Relative path
            seed = "/".join([dst, s.split("/./")[1]])
            while '//' in seed:
               seed = seed.replace('//','/')
            assert(relative != False)
            relative = True
         else:
            seed = "/".join([dst, os.path.basename(s)])
            assert(not relative)
            relative = False

         choices = self.pickdstnodes(seed, pickn, hashbasename)
         for c in choices:
            dictListAppend(nodesrcs, c.name, s)

      if remove:
         redundants = set(srcs)
         if self.thisname in nodesrcs:
            #print >>sys.stderr, 'Remove', nodesrcs[self.thisname], 'from', redundants
            redundants -=  set(nodesrcs[self.thisname])
      else:
         redundants = None

      if relativeroot and self.thisname in nodesrcs:
         # Remove no-op copy to self (which could actually delete the files)
         nodesrcs.pop(self.thisname)

      self.rsyncput(nodesrcs, dst, serialize, procs, tag)

      return redundants

   def pickdstnodes(self, dst, pickn, hashbasename):
         # We always specify a seed when calling pick() so there is stability in which nodes work is mapped to.
         # It's nice if they go to nodes that might have already received the store in a previous execution.
         dst = dst.replace("/./","/")
         dst = dst.replace("//","/")
         if pickn:
            # Pick which nodes get this file
            if hashbasename:
               seed = os.path.basename(dst)

               # If we're just using basename, we're probably in a redistribute and there will be a lot of reoccurrences of the same basename, so cache the pickn() results.
               if pickn not in self.cached_dstnodes:
                  self.cached_dstnodes[pickn] = {}
             
               if seed in self.cached_dstnodes[pickn]:
                  #print >>sys.stderr, "PICK CACHE", hashbasename, pickn, seed, [c.hostname for c in self.cached_dstnodes[pickn][seed]]
                  return self.cached_dstnodes[pickn][seed]
            else:
               seed = dst

            if type(pickn) is int:
               choices = self.pickn(seed=seed, n=pickn)

            else:
               # use default n
               choices = self.pickn(seed=seed)

            choices = [self.config.locs[c] for c in choices]

            if pickn and hashbasename:
                # Add to cache
                self.cached_dstnodes[pickn][seed] = choices

            #print >>sys.stderr, "PICK", hashbasename, pickn, seed, choices, [c.hostname for c in choices]

            return choices
         else:
            # Use all destinations that are active
            retlist = []
            for c in self.config.locs:
               if not self.config.locs[c].inactive:
                  retlist.append(self.config.locs[c])
            return retlist

   def rsyncput(self, nodesrcs, dstdir, serialize, procs, tag):
      # nodesrcs is a dictionary indexed by nodenames each containing a list of fully-qualified local srcs.
      # Iff relative is True, then the local source should contain a /./ element and path elements after /./ will be created in the dst.
      # Iff serialize is True, then do one node at a time.
      # tag is used solely for verbose status reporting.

      dsts = list(nodesrcs.keys())
      random.shuffle(dsts)
      i = 0
      for dst in dsts:
         i += 1
         if serialize:
            if serialize > 1:
               queue = "rr" + str(i % serialize)
            else:
               queue = "serialize"
         else:
            queue = dst

         self.rsync(False, dst, nodesrcs[dst], dstdir, queue, procs, tag)

   def rsync(self, is_get, node, inputlist, dstdir, queue, procs, tag):
      # Build rsync style "hostname:/path/to/root" specifications
      loc = self.config.locs[node]
      remoteroot = loc.rootdir
      remotepath = remoteroot
      if isremote(loc.hostname):
         remotepath = loc.hostname + ":" + remotepath

      if is_get:
         # The remote paths may contain wildcards, so we have to use --include-from instead of --files-from
         # Also the remote side might be a directory, so we use -r
         srcpath = remotepath + "/"
         dstpath = dstdir
         flags = ["-rp", "--include-from=-", "--exclude=*"]
         il = []
         for name in inputlist:
            # Clean up double slashes
            while '//' in name:
               name = name.replace('//','/')

            # remote source doesn't seem to process /./ relative paths (which we rely on for local source)
            name = name.replace('/./', '/')

            # Any name could be a directory, so add a recursive mask to get its children
            il.append(os.path.join(name, "***"))

            # Any name could be a file, so add it without a /***
            il.append(name)

            # we have to explicitly include every parent directory as well
            name = os.path.dirname(name)
            while name and name != "/":
               il.append(name + "/")
               name = os.path.dirname(name)

         inputlist = il
         
      else:
         # We have resolved all the wildcards for node assignment, so just generate a list of files
         if inputlist[0][0] == "/":
            srcpath = "/"
         else:
            srcpath = "."

         dstpath = remotepath + "/" + dstdir 
         while '//' in dstpath:
            dstpath = dstpath.replace('//','/')
            
         flags = ["-R", "--files-from=-"]

      inputstr = '\n'.join(inputlist).encode('utf-8')

      cmd = self.this.rsynccmd + ["-utLde", loc.ssh] + flags + [srcpath, dstpath]

      #print >>sys.stderr, "inputlist:", inputlist
      procs.Popen(cmd, queue=queue, stdinstr=inputstr, node=node, tag=tag)


   def get(self, args, procs=None, outfile=sys.stdout, relative=False):
      """Copy files from the cloud to local storage.

Note that if the source is wildcard, then output will be put in a 
sub-directory of the destination.  The name of that subdirectory 
will be the directory name preceding the first wildcard."""
      p = MethodOptionParser(fixed=["src... [dst]"])
      p.add_option("-c", "--cat", action="store_true", help="Cat files to stdout (do not specify a destination)")
      p.add_option("-n", "--name", action="store_true", help="Show file name when catting files")
      p.add_option("-e", "--errors", action="store_true", help="Handle .stderr files specially")
      (options, args) = p.parse_args(args)

      if (not options.cat) and (len(args) < 2):
         p.print_help()
         return 1
      
      ## rsync really (suprisingly) only supports relative anyway 
      #if relative:
      #   args = ["/./" + a for a in args]
      #else:
      #   args = [os.path.dirname(a) + '/./' + os.path.basename(a) for a in args]

      if options.cat:
         dst = mkdtemp(prefix="get") + "/"
         srcs = args
      else:
         dst = args[-1]
         srcs = args[:-1]

      for loc in self.config.locs.values():
         if loc.inactive: continue
         self.rsync(True, loc.name, srcs, dst, loc.name, self.procs, "get %s" % (' '.join(args)))

      self.procs.collect()

      if options.cat:
         empty = True
         for (dirpath, dirnames, filenames) in os.walk(dst):
            for f in filenames:
               if f == ".status":
                  #cat'ing .status files is never(?) the right answer and rsync tends to fetch .* along with *
                  continue
               fname = os.path.join(dirpath, f)
               if os.path.getsize(fname):
                  relname = fname[len(dst):]
                  if f == ".stderr" and options.errors:
                     print("=== %s ===" % relname, file=sys.stderr)
                     sys.stderr.writelines(open(fname))
                     print("======", file=sys.stderr)
                  else:
                     if options.name:
                        print("=== %s ===" % relname, file=outfile)
                     outfile.writelines(open(fname))
                  empty = False
         if options.name and not empty:
            print("======", file=outfile)

         shutil.rmtree(dst)

      return self.procs

   def processes(self):
      return sum(i.cpusperjob for i in self.config.locs.values())
         
class FmLocation(SmartDict):
   def subst(self, args):
       return [n.replace("%(ROOTDIR)", self.rootdir).replace("%(SYNCDIR)", self.syncdir).replace("%(NODE)", self.name) for n in args]

class Poll:
   def __init__(self):
      try:
        self.pollobj = select.poll()
        self.kqueue = None
      except:
        self.kqueue = select.kqueue()
        self.pollobj = None
        self.reads = set()
        self.writes = set()

   def add(self, fd, for_read=False, for_write=False):
      if self.pollobj:
         mask = 0
         if for_read:
            mask |= select.POLLIN
         if for_write:
            mask |= select.POLLOUT

         self.pollobj.register(fd, mask|select.POLLHUP|select.POLLERR) 

      else:
         #print >>sys.stderr, "POLL add", fd, for_read, for_write
         if for_read:
            self.reads.add(fd) 
            self.kqueue.control([select.kevent(fd, select.KQ_FILTER_READ, select.KQ_EV_ADD, fflags=select.KQ_NOTE_LOWAT)], 0)
         if for_write:
            self.writes.add(fd) 
            self.kqueue.control([select.kevent(fd, select.KQ_FILTER_WRITE, select.KQ_EV_ADD)], 0)

   def unregister(self, fd):
      if self.pollobj:
         self.pollobj.unregister(fd)
      else:
         #print >>sys.stderr, "POLL unregister", fd, fd in self.reads
         if fd in self.reads:
            self.kqueue.control([select.kevent(fd, select.KQ_FILTER_READ, select.KQ_EV_DELETE)], 0)
            self.reads.remove(fd)

         if fd in self.writes:
            self.kqueue.control([select.kevent(fd, select.KQ_FILTER_WRITE, select.KQ_EV_DELETE)], 0)
            self.writes.remove(fd)

   def poll(self, timeout):
      if self.pollobj:
         try:
            l = self.pollobj.poll(timeout)
         except select.error as e:
            if e[0] == errno.EINTR:
               return
            else:
               raise

         for fd,event in l:
            if event & select.POLLIN:
               yield (fd, 'r')
            if event & select.POLLOUT:
               yield (fd, 'w')

      else:
         #print >>sys.stderr, "POLL poll", timeout
         if not self.reads and not self.writes:
            #print >>sys.stderr, "Skipping poll with nothing registered"
            return

         if timeout == -1:
            timeout = None
      
         events = self.kqueue.control(None, 1, timeout)
         for e in events:
            if e.filter == select.KQ_FILTER_READ:
               yield (e.ident, 'r')
            elif e.filter == select.KQ_FILTER_WRITE:
               yield (e.ident, 'w')
            else:
               print("unknown filter", e, file=sys.stderr)

class Procs:
   """This class is used to launch some number of child processes and reap them.
   It provides methods to instantiate a process for each node."""

   def __init__(self, retries=0):
      self.queues = {}
      self.poll = Poll()
      self.fd2proc = {}
      self.pids = {}
      self.numprocspolling = 0
      self.retries = retries

   def isempty(self):
      return (not self.pids)

   def Popen(self, cmdv, **kwargs):
      kwargs['cmdv'] = cmdv
      queue = kwargs.get('queue')
      if not kwargs.get('tag'):
         kwargs['tag'] = cmdv[0] + b'...'
      if not kwargs.get('retries'):
         kwargs['retries'] = self.retries
      
      if queue and self.queues.get(queue) != None:
         # If queue exists (even if it is an empty queue), then something is running
         if Verbose > 2:
            print("Queueing", kwargs['tag'], "to", queue, len(self.queues[queue]), file=sys.stderr)
         self.queues[queue].append(kwargs)
         return
      else:
         # No queue, means we can run now, but create an empty queue to block subsequent tasks         
         self.queues[queue] = []
         return self._PopenSave(**kwargs)

   def _PopenSave(self, **kwargs):
      # Call _PopenNow, but save a copy of the kwargs for later retries
      proc = self._PopenNow(**kwargs)
      proc.kwargs = kwargs
      return proc

   def PopenWithPipes(self, cmdv, stdin=None, stdout=None, stderr=None, **kwargs):
      """This is a wrapper for subprocess.Popen that supports pipelines as in Popen(["ls", "|", "wc", "-l"])"""

      results = []
      thiscmd = []
      for i in range(len(cmdv)):
         if cmdv[i] == b'|':
            # There are more words, so make an intermediate pipe
            try:
               r = subprocess.Popen(thiscmd, stdin=stdin, stdout=subprocess.PIPE, stderr=stderr, close_fds=True, **kwargs)
            except:
               print("Error", sys.exc_info()[1], "executing", thiscmd, file=sys.stderr)
               raise
  

            # Next element of the pipe gets this output
            stdin = r.stdout

            results.append(r)
            thiscmd = []
         else:
            thiscmd.append(cmdv[i])

      # This is the last command in the pipeline
      if thiscmd:
         try:
            r = subprocess.Popen(thiscmd, stdin=stdin, stdout=stdout, stderr=stderr, close_fds=True, **kwargs)
         except:
            print("Error", sys.exc_info()[1], "executing", thiscmd, file=sys.stderr)
            raise
         results.append(r)

      # Here's how we handle these pipelines outside of this function.  One (that last one)
      # will be returned up the call stack and tracked as the unit of work.  All
      # will be placed in the reaping and polling datastructures and handles accordingly.
      # Only when all of the parts left will the tracked one be returned up and passed to FinalizeItem.

      # Now close our reference to intermediate pipes so we don't poll on them
      for i in range(1, len(results)):
         if results[i].stdin:
            #results[i].close()
            results[i].stdin = None

      if len(results) > 1:
         for i in range(len(results)):
            results[i].partof = results[-1]

         # We will count this down (including self) to known when this pipeline/Item is done computing
         results[-1].parts_left = len(results)
      else:
         results[-1].partof = None
   
      for i in range(0, len(results) - 1):
         results[i].stdout = None

      results[-1].parts = results[:-1]

      return results

   def add_poll(self, fh, r, for_read=False, for_write=False):
      fd = fh.fileno()
      self.poll.add(fd, for_read, for_write)
      self.fd2proc[fd] = r
  
      # make non-blocking file
      fl = fcntl.fcntl(fd, fcntl.F_GETFL)
      fcntl.fcntl(fd, fcntl.F_SETFL, fl | os.O_NONBLOCK)
 
   def _PopenNow(self, cmdv=[], prefix=None, stderr=subprocess.PIPE, stdout=subprocess.PIPE, call=False, tag=None, queue=None, node=None, stdinstr=None, cwd=None, retries=None):
      # This function should only be called by _PopenSave

      # Note, we prefer to have a stdout so that poll() can tell when it closes and then reap the child

      if stdinstr:
         stdin = subprocess.PIPE
      else:
         stdin = open('/dev/null')

      first = True
      for r in self.PopenWithPipes(cmdv, stdin=stdin, stdout=stdout, stderr=stderr, cwd=cwd):
         r.stdinstr = None # Default to nothing to finalize

         if r.stderr or r.stdout or (first and stdinstr):
            self.numprocspolling += 1
            if r.stdout:
               self.add_poll(r.stdout, r, for_read=True)
               r.stdoutbuf = io.BytesIO()
   
            if r.stderr:
               self.add_poll(r.stderr, r, for_read=True)
               r.stderrbuf = io.BytesIO()
   
            if first and stdinstr:
               self.add_poll(r.stdin, r, for_write=True)
               r.stdinstr = stdinstr
               self.processStdin(r) 
  
         first = False
 
         r.tag = tag
         r.start = time.time()
         r.queue = queue

         if queue and not node:
            node = queue
         r.node = node
         r.cmd = cmdv
      
         self.pids[r.pid] = r
         if Verbose > 2:
            print(r.pid, cmdv, r.node, file=sys.stderr)
   
      return r  #Last one, and the one that others are "partof"
   
   def wakeup(self, qname):
         if not qname:
            return

         #Wake-up anything on this queue
         if self.queues[qname]:
            kwargs = self.queues[qname].pop(0)
            # Leave queue, even if empty, so things wait for us to finish
            if Verbose > 2:
               print("Waking", kwargs, file=sys.stderr)
            self._PopenSave(**kwargs)
         else:
            # Queues was already empty, so now delete it
            del self.queues[qname]

   def collect(self, ignoreErrors=False, labelPrint=False, maxErrors=None, markInactive=False, stopOnError=False):
      """Execute any active or queued processes and return, a count of the number of errors and a list of the processes objects that ran."""
      results = []
      errors = 0
      total = 0
      stopping = False
      while True:
         # Block if not stopping (if stopping, reap everything that's done already and then stop)
         p = self.waitpid(not stopping)
         if p == None:
            break

         results.append(p)
         total += 1

         if p.status:
            errors += 1 
            if stopOnError:
               print("Terminating early due to an error", file=sys.stderr)
               stopping = True

         if Verbose > 2:
            ec = os.WEXITSTATUS(p.status)
            print("%s: %s status %d for %s" % (p.queue, seconds2human(p.time), ec, p.tag), file=sys.stderr)
            waiting = [l.queue for l in self.pids.values()]
            waiting.sort()
            if waiting and len(waiting) < len(results):
               print("Still waiting on", ' '.join(waiting), file=sys.stderr)

      if not results:
         return None, results

      tag = "for " + results[0].tag #XXX not al tags identical

      if stopping or (Verbose > 1):
         print("--- Report", tag, file=sys.stderr)
         tag = ""
         mean = 0.0
         for p in results:
            mean += p.time
        
         mean /= len(results)
         stddev = 0.0
         for p in results:
            stddev += (p.time - mean)**2

         stddev /= len(results)
         stddev = math.sqrt(stddev)

         if stddev > 0:
            for p in results:
               deviations = (p.time - mean) / stddev
               if deviations > 2:
                  print("Node %s slow by %g standard deviations" % (p.node, deviations), file=sys.stderr)

            print("Average time %gs, max %gs, stddev %gs %s" % (mean, max([p.time for p in results]), stddev, tag), file=sys.stderr)

      if not stopping:
         for k,v in self.queues.items():
            assert(not v)
         assert(not self.pids)
         assert(self.numprocspolling == 0)

         self.poll = Poll() #Reinit, just in case not everything was unregister()'d

      if not ignoreErrors and errors:
         print("Error, %d/%d subprocess(es) returned error %s" % (errors, total, tag), file=sys.stderr)

      if labelPrint:
         sys.stdout.write(coallesce([f.stdout for f in results], [f.node for f in results]))
      if stopping or labelPrint or Verbose > 0:
         sys.stderr.write(coallesce([f.stderr for f in results], [f.node for f in results]))

      if Verbose > 1:
         print("---", file=sys.stderr)

      if stopping:
         return None

      if not ignoreErrors and errors:
         if maxErrors != None and errors > maxErrors:
            print("Terminating early due to %d errors" % errors, file=sys.stderr)
            sys.exit(errors)

      if markInactive:
         failed = [p.node for p in results if p.status]
         if failed:
            print("Marking nodes inactive: %s" % ','.join(failed), file=sys.stderr)
            for f in failed:
               markInactive.locs[f].inactive = True

      return errors, results


   def poll_remove(self, fh):
      # Make blocking again
      fd = fh.fileno()
      fl = fcntl.fcntl(fd, fcntl.F_GETFL)
      fcntl.fcntl(fd, fcntl.F_SETFL, fl & (~os.O_NONBLOCK))

      self.poll.unregister(fd)

      del self.fd2proc[fd]

   def finalizeProc(self, p):
      # Record compute time
      after = os.times()
      p.time = time.time() - p.start
      p.utime = after[2] - p.starttimes[2]
      p.stime = after[3] - p.starttimes[3]
      del p.starttimes

      # Finish building the output buffers
      if p.stdout != None:
         self.poll_remove(p.stdout)

         #print >>sys.stderr, "finalized", p.pid, p.stdout.fileno()
         p.stdoutbuf.write(p.stdout.read())
         p.stdout = p.stdoutbuf
         p.stdout.seek(0)

      if p.stderr != None:
         self.poll_remove(p.stderr)

         p.stderrbuf.write(p.stderr.read())
         p.stderr = p.stderrbuf
         p.stderr.seek(0)

      if p.stdinstr != None:
         self.poll_remove(p.stdin)

      if p.stderr or p.stdout:
         self.numprocspolling -= 1

      del self.pids[p.pid]

      if p.partof:
         p.partof.parts_left += -1
         #p.partof.part_status.append(p.status)
         #print >>sys.stderr, "PARTOF STATUS", p, p.status, p.time
         # only the acountable child should impact queueing, and doesn't really count to caller
         if p.partof.parts_left:
            return None
         else:
            # Now that p has finished, p.partof is complete, so process the overall (which may or may not be p)
            p = p.partof

      # XXX: ssh returns 255 if it can't connect and rsync returns 12
      if p.status and p.kwargs['retries'] and (os.WEXITSTATUS(p.status) == 255 or os.WEXITSTATUS(p.status) == 12):
         # Requeue if retries enabled and child returned 255 (SSH failed to connect)
         if Verbose > 0:
            print(p.kwargs['retries'], "more retries for", p.node, file=sys.stderr)
         p.kwargs['retries']  -= 1
         time.sleep(2**(self.retries - p.kwargs['retries'] - 4) + 0.5 * random.random())
         self.queues[p.queue].append(p.kwargs)
         self.wakeup(p.queue)
         return None
     
      self.wakeup(p.queue)

      return p


   def waitpid(self, block=False):
      """Check for any completed child, remove them from the procs dictionary and return them."""

      while not self.isempty():
         r = self.checkwait(block=block)
         if r:
            return r
         if not block:
            break

      return None

   def checkwait(self, block=False):
      if block:
         # First, the block argument is just a hint, we're not obligated to block.
         # Second, we may have children that are blocking on I/O to us, so we have use poll().
         # But we may have children that have no shared fd with us and that can only be reaped with waitpid().
         # So we need to figure out which case it is to determine where we can actually block.

         if self.numprocspolling == len(self.pids):
            # In this case, waitpid() is superfluous, so don't block on it, but
            # block on poll()
            waitopts = os.WNOHANG
            pollopts = -1 # Block
         elif self.numprocspolling:
            # In this case we have to bounce back between waitpid() and poll()
            # We don't want to have a complete busy loop, so we give poll a small timeout.
            # This creates some potential latency, but this is not a expected case
            print("Debug: inefficient when only some children have fds we manage", file=sys.stderr)
            waitopts = os.WNOHANG
            pollopts = 2500 # block for 2500ms
         else:
            # In this case poll() is superfluous and we should just do a blocking waitpid()
            waitopts = 0 #block
            pollopts = 0 #do not block
      else:
         # Simple case
         pollopts = 0 # poll only
         waitopts = os.WNOHANG

      #print >>sys.stderr, "block case", waitopts, pollopts

      # Check for completed children.
      try:
         # Waiting register's child's CPU times, so measure right before and after
         starttimes = os.times()

         (pid, status) = os.waitpid(0, waitopts) 
         if pid:
            p = self.pids[pid]
            p.status = status
            p.starttimes = starttimes
            return self.finalizeProc(p)

      except OSError as e:
         if e.errno == errno.ECHILD:
            # If we're here its probably because in python 2.4, subprocess reaps other children
            # whenever making a new one.  So one of the children we thought was running had already
            # been waitpidded.  http://bugs.python.org/issue1731717
            # So, poll on each of our children to find the one to finalize:
            for p in self.pids.values():
               # First look for things reaped by the signal handler
               if 'error' in p.__dict__:
                  return self.finalizeProc(p)

               # Since the child is already reaped, we'll probably measure no CPU time for it. oh well
               starttimes = os.times()
               status = p.poll()
               if status != None:
                  p.status = status
                  return self.finalizeProc(p)    

            print("Unexpected: no child", self.pids, file=sys.stderr)
            raise
         else:
            raise

      # Look for children that may be blocking on writes to stdout, or that have finished
      # this won't catch children that we don't have share a fd with

      # Make sure we get interrupted if a child exits (in case we're not connected to any of its fds)
      for fd, event in self.poll.poll(pollopts):
         p = self.fd2proc[fd]

         if event == 'r':
            if fd == p.stdout.fileno():
               s = p.stdout.read()
               p.stdoutbuf.write(s)
            else:
               assert(fd == p.stderr.fileno())
               s = p.stderr.read()
               p.stderrbuf.write(s)
         if event == 'w':
            assert(fd == p.stdin.fileno())
            self.processStdin(p)

      return None

   def processStdin(self, p):
      assert(p.stdinstr != None)
      s = p.stdinstr
      try:
         # Child could quit before we get it all out
         numbytes = os.write(p.stdin.fileno(), s)
         #print >>sys.stderr, "%s: wrote %d of %d bytes" % (p, bytes, len(p.stdinstr))
         p.stdinstr = p.stdinstr[numbytes:]

      except IOError:
         raise
         # assume that child exit status will tell the story
         # if it ignored some input and exited with 0, we'll be oblivious
         p.stdinstr = None

      if not p.stdinstr:
         #print >>sys.stderr, "%s: closing stdin pipe, %d" % (p, p.stdin.fileno())
         del self.fd2proc[p.stdin.fileno()]
         try:
             # May be closed
             self.poll.unregister(p.stdin.fileno())
         except ValueError:
             pass
         p.stdin.close()
         p.stdinstr = None  #Tell finalize not to bother closing

# The design is as follows:
#   1. Jobs are submitted in an uncoordinated manner, so they have unique
#      identifiers that aren't generated by the user. but that are identical
#      across all nodes running a job. 
#   2. To manage the problem of listing jobs and removing jobs, we use a 
#      directory structure to contain all current jobs.  Deleting a file should
#      (eventually) lead to a job not running further.
#   3. New jobs should be invoked synchrously by calling a job scheduler with a
#      hint that points to the job.  Failure to send this hint should only delay
#      the job scheduler discovering the job since it should periodically poll
#      for changes in the job directory.

class JobScheduler:
   """JobScheduler maintains a set of child processes working on a set of jobs."""

   def __init__(self, locs):
      self.jobs = {}  # A dictionary of job objects indexed by job name
      self.procs = Procs(retries=0)
      self.options = locs.this
      self.freethreads = self.options.processes
      self.locker = locs.getSynchronizer()

      if self.options.dynamicload:
         global cpu
         cpu = CpuProfile(locs, self.options.dynamicload)

   def ReadJobDir(self):
      """Check for new/removed jobs"""

      jobs = os.listdir(self.options.jobdir)
      removed = set(self.jobs) - set(jobs)
      recent = set(jobs) - set(self.jobs)
      for j in removed:
         #print "Job", j, "removed"
         del self.jobs[j]

      for j in recent:
         if j.startswith("."):
            # Ignore dot files (probably rsync droppping something in the directory)
            continue

         #print "Job", j, "added"
         jobuid = os.stat(self.options.jobdir + "/" + j).st_uid
         if jobuid != os.getuid():
            #print >>sys.stderr, "Skipping job owned by UID %d", jobuid
            continue
         try:
            self.jobs[j] = FmJob(self.options.jobdir + "/" + j, cpusPerJob=self.options.cpusperjob, locker=self.locker)
         except:
            traceback.print_exc()
            print("Error parsing job description", j, "; skipping", file=sys.stderr)

   def RunOnce(self, invalidateOnly=False):
         """Try to launch a work item and return True on success (None->nothing to do)"""

         if self.options.dynamicload and not self.procs.isempty() and not cpu.available(len(self.procs.pids)):
            # If using dynamic scheduling and something is running and system is not idle, 
            # then don't schedule more work.
            return None

         self.freethreads -= 1

         # Look for something with work to do
         jobs = list(self.jobs.keys())
         random.shuffle(jobs)
         for jobname in jobs:
            j = self.jobs[jobname]

            if (not self.options.dynamicload) and (len(j.running) >= j.threads):
               continue

            proc = j.compute(self.options, self.procs, invalidateOnly)
            if invalidateOnly:
               continue

            if self.options.dynamicload:
               # Restart our checking of idleness
               cpu.update(force=True)

            #print >>sys.stderr, "Launched", proc
            if proc:
               return True
            else:
               # No more work to do, check to see if job is complete
               # Note, job cannot be complete if parent is still active
               if not j.continuous and not j.running and (not j.parent or j.parent not in self.jobs):
                  self.JobDone(jobname)

         self.freethreads += 1
         return None

   def JobDone(self, jobname):
      """A job has run to completion, remove it locally."""

      del self.jobs[jobname]
      #print >>sys.stderr, "Job", jobname, "done"
      os.unlink(self.options.jobdir + "/" + jobname)

   def RunUntilDone(self):
      """Run until there is no more input on it.  Return True iff we did something"""

      didSomething = False
      sleep = 0.01

      # Invalidate anything that is stale from previous runs
      self.RunOnce(invalidateOnly=True)

      while True:
         if self.freethreads:
            self.ReadJobDir()
            if self.procs.isempty() and not len(self.jobs):
               # Doing nothing and no more jobs to run
               return didSomething
            if self.RunOnce():
               didSomething = True
               block = False
            else:
               # Nothing to do right now
               # Don't return because we're still working,
               # but wait before we look for more work to do.
               #print >>sys.stderr, "Wait for completion (and/or more work)"

               # XXX. Check syncfiles for all active procs and see if somebody
               # finishes before us.  If so, abort (we may be the a slow node).
               # Only check here since that's when we're on our last work item (no more work to do)
               # and could accelerate our wait finishing sooner by terminating.
               #for p in self.procs:
               #   check to see if somebody beat us

               # Sleeping hurts latency for detecting new inputs, but avoids busy waits.
               # So we do an exponential backoff in how long we sleep with a max of 1 second
               sleep *= 1.1
               if sleep > 1:
                  sleep = 1  # Max out at 1 sec sleep
               block=False # Don't block since new work could arrive before a child finishes
         else:
            block = True
            assert (not self.procs.isempty())

         p = self.procs.waitpid(block=block)
         #print >>sys.stderr, "WAITPID", block, p
         if p:
            self.freethreads += 1
            self.finalizeItem(p)
            if p.status and p.job.checkexit != None:
               if isinstance(p.inputs, list) and len(p.inputs) > 1:
                  inputstr = str("%s and %d others" % (str(p.inputs[0]), len(p.inputs)-1))
               else:
                  inputstr = str(p.inputs)
               print("Node terminating job %s due to exit status %d on input %s:" % (p.jobname, p.status, inputstr), file=sys.stderr)
               try:
                  sys.stderr.write(open(p.outdirname+"/"+p.outbasename+"/.stderr").read())
               except IOError:
                  # .stderr file might not exist
                  pass

               # Do not cleanup job because the presence of jobs after the scheduler exits is how the waiter detects an error
               #self.JobDone(p.jobname)

               return

            if self.options.dynamicload:
               cpu.update(force=True)
            sleep = 0.01
         else:
            if not block:
               time.sleep(sleep)


   def finalizeItem(self, p):
      stats = {}
      stats['status'] = p.status
      stats['time'] = p.time
      stats['utime'] = p.utime
      stats['stime'] = p.stime
      stats['inputsize'] = p.inputsize
      stats['jobname'] = p.jobname
      stats['start'] = p.start
      stats['nodename'] = self.options.name
      stats['hostname'] = Hostname
      stats['timestamp'] = time.time()
      stats['cmd'] = p.cmd

      if p.parts:
         assert(not p.parts_left)

         for r in p.parts:
            if stats['status'] == 0:
               # Promote from non-error to error (like pipefail)
               stats['status'] = r.status
            stats['time'] += r.time
            stats['utime'] += r.utime
            stats['stime'] += r.stime
            stats['start'] = min(stats['start'], r.start)
 
      dir = p.outdirname + "/." + My_file_prefix + "_" + p.outbasename
      try:
         f = open(dir + "/.status", "wb")
      except IOError:
         # Perhaps we were invalidated while running.  Don't sweat it.
         p.job.running.remove(p)
         return

      pickle.dump(stats, f, protocol=2)
      f.close()

      # Remove empty outputs to avoid unnecessary downstream processing
      for f in "stdout", ".stderr":
         outf = dir + "/" + f
         if os.path.getsize(outf) == 0:
            os.unlink(outf)

      self.locker.done(p.outrelpath, p.start)
   
      dst = p.outdirname + "/" + p.outbasename 

      tmp = p.outdirname + "/.del." + My_file_prefix + "_" + p.outbasename
      try:
         # By removing this dst(if present) , we're invalidating any previously derived data, but our redo-if-newer-than logic will handle the compute.
         # XXX. There is still a chance for a race if a child already was in process on the old dir and in between multiple files.
         os.rename(dst, tmp)
         shutil.rmtree(tmp)
      except OSError as e:
         if e.errno == errno.ENOENT:
            # Didn't exist (or race to delete).  This is common and okay.
            pass
         else:
            raise

      try:
          os.rename(dir, dst)
      except OSError as e:
         if e.errno == errno.EEXIST or e.errno == errno.ENOTEMPTY:
            print("Warning: unable to finalze to %s (okay if this is a shared directory):" % dst, file=sys.stderr)
            #traceback.print_exc()
         else:
            raise

      p.job.running.remove(p) 

     
class CpuProfile:
   def __init__(self, locations, interval):
      self.interval = interval
      self.idle = 0
      self.total = 0
      self.HZ = os.sysconf('SC_CLK_TCK')
      self.ncpus = os.sysconf('SC_NPROCESSORS_ONLN')

      self.divisor = 0
      hostname = locations.this.get('hostname')
      for l in locations.config.locs.values():
         if (hostname == l.get('hostname')):
            self.divisor += 1
           
      if Verbose > 2:
         print("Host", hostname, "shared with", self.divisor, file=sys.stderr)

      if not self.divisor:
         print("Warning: could not determine number of nodes on this host", file=sys.stderr)
         self.divisor = 1 

   def update(self, force=False):
      """Try to update CPU idle figures.  Return True iff we updated the idle figures."""
      try:
         fields = open('/proc/stat').readline().split()
      except:
         print("Warning: scheduler cannot determine CPU idle % on this platform", file=sys.stderr)
         return False

      assert(fields[0] == "cpu")
      fields = [int(x) for x in fields[1:]]
      total = sum(fields)

      # Make sure our update is large enough to be meaningful
      duration = float(total - self.total)
      duration_wallclock = duration / self.HZ / self.ncpus
      if (not force) and duration_wallclock < self.interval:
         if Verbose > 2:
            print(time.asctime(), "DynamicLoad: Waiting to gather more stats", file=sys.stderr)
            # We don't sleep since we're called by RunOnce which is an event management loop
         return False
      
      idlecpu = fields[3]

      if duration:
         self.idle_fraction = (idlecpu - self.idle) / duration
      else:
         self.idle_fraction = 0

      if (not force) and Verbose > 1:
         print(time.asctime(), "DynamicLoad: CPU ", self.idle_fraction * 100, "% idle over ", duration_wallclock, "seconds", file=sys.stderr)

      self.idle = idlecpu
      self.total = total
 
      return True

   def memory_usage(self):
      #return 1 - (os.sysconf('SC_AVPHYS_PAGES') / float(os.sysconf('SC_PHYS_PAGES')))
      f = open("/proc/meminfo") 
      free = 0.0
      for line in f:
         if line.startswith("MemTotal"):
            total = float(line.split()[1])
         if line.startswith("MemFree"):
            free += float(line.split()[1])
         if line.startswith("Cached"):
            free += float(line.split()[1])
            f.close()
            return 1 - (free/total)

      assert(not "Unable to parse /proc/meminfo")

   def available(self, nprocs):
      """Return True iff the system is neither CPU nor I/O bound."""
      if not self.update():
         return False

      percent_per_proc = (1.0 - self.idle_fraction) / self.divisor / nprocs 
      percent_per_cpu = 1.0 / self.ncpus

      # Use a threshold that assumes that a job will use at least 1 CPU (percent_per_cpu) and perhaps much more (percent_per_proc).
      # If the actual requirement is less than 1 CPU's worth, we'll add more in the futures.
      threshold = max(percent_per_cpu, percent_per_proc)

      # Check for idle CPU time
      if self.idle_fraction < (1.0 / self.ncpus):
         # Less than 1 CPU's worth of resources is available, so don't add more

         if Verbose > 2:
            print(time.asctime(), "DynamicLoad: Waiting for CPU to be more idle", file=sys.stderr)
         return False

      mem_usage = self.memory_usage()

      # Assume current memory usage is evenly distributed across our peer schedulers:  
      #		our_usage = mem_usage / self.divisor

      # Assume how much memory a new child would take:
      #		needed = our_usage / nprocs

      # Assume available memory is evenly distributed across schedulers
      #		available_share = (1.0 - mem_usage) / self.divisor
    
      # We should wait if (needed > available_share)
      #                 = mem_usage * (1.0 / nprocs) > (1.0 - mem_usage) 
      #                 = mem_usage + mem_usage * (1.0 / nprocs) > 1.0 
      #                 = mem_usage * (1 + (1.0 / nprocs)) > 1.0 
      #                 = mem_usage > 1.0 / (1 + (1.0 / nprocs))
      #                 = mem_usage > 1.0 / ((nprocs + 1) / nprocs)
      #                 = mem_usage > nprocs / (nprocs + 1)
      #                 = mem_usage > nprocs / (nprocs + 1)

      if nprocs:
         threshold = nprocs / (nprocs + 1.0)

         if mem_usage > threshold:
            # Wait for more memory
            if Verbose > 1:
               print(time.asctime(), "DynamicLoad: Waiting for memory usage to drop to %d%% from %d%%" % (int(100*(threshold)), int(100*mem_usage)), file=sys.stderr)
            return False
   
      # Account for D state:
      # If we're in I/O wait (e.g. for a write), then we're not idle,
      # so that's already accounted for.  But if we're in D, then we are
      # idle, but we don't want more D.  The kernel only seems to tally D
      # in the loadavg, but that's exponentially slow, we need to go tally it
      # ourself

      # XXX. would like to limit this to just our disk

      unint = 0
      for f in os.listdir('/proc'):
         if f.isnumeric(): # looks like a pid
            try:
                line = open('/proc/' + f + '/stat').readline().split()
            except:
                # probably finished, just ignore
                continue

            if line[2] == 'D':
                unint += 1

      if not unint:
         return True
      else:
         if Verbose > 1:
            print(time.asctime(), "DynamicLoad: Waiting for less D state (currently %d)" % (unint), file=sys.stderr)

         #Restart accounting so we don't include previous D time
         self.update(force=True) 

         return False


class FmJob:
   """Each FmJob object represents a job, as specified in a job file, and
    provides methods for identifying and processing inputs for that job."""

   def __init__(self, fname, cpusPerJob = 1, locker = None):
      self.locker = locker

      config = configparser.ConfigParser()

      def config_get(field, default=None, raw=False):
         if config.has_option("mrjob", field):
            return config.get("mrjob", field, raw=raw)
         else:
            return default

      processed = config.read(fname)
      if not processed:  
         raise IOError(errno.ENOENT, "Could not open file", fname)

      self.jobname = os.path.basename(fname)
      self.cmd = config_get("cmd", raw=True)
      try:
         self.cmd = eval(self.cmd)
      except:
         self.cmd = self.cmd.split()
      self.inputs = config_get("inputs")
      self.cachedinputs = None
      self.cachedinputs_deferred = []
      self.previousinputs = None
      self.continuous = config.has_option("mrjob", "continuous")
      self.reduce = config_get("reduce")

      self.threads = int(config_get("procspercpu", 1))
      self.threads *= cpusPerJob

      self.running = []

      self.parent = config_get("parent")
      self.checkexit = config_get("checkexit")
      if self.checkexit != None:
         self.checkexit = int(self.checkexit)

   def compute(self, options, procs, invalidateOnly):
      # First time thru we expand the input globs to a file list
      # Unless this is a continuous job, this will be the only time we enumerate the files
      if not self.cachedinputs:
         glob = [options.rootdir + "/" + x for x in self.inputs.split()]
         glob = multiglob(glob)

         if options.cowdir:
            cows = multiglob([options.cowdir + "/" + x for x in self.inputs.split()])

            if self.reduce:
                glob += cows

            else:
                # Assume that COWdir is globally shared and manage competition/duplication of processing it.
                # Use demand setting to limit contention (unlike files in the rootdir)
                n = Locations.this.demand

                if n == 0:
                    # Process everything in sight
                    glob += cows
    
                else:
                   for i in cows:
                      choices = list(Locations.pickn(i[len(options.cowdir):], n=n))
                      if Locations.thisname in choices:
                         #print >>sys.stderr, i[len(options.cowdir):], "hashes to", list(choices), i
                         glob.append(i)
    
         if self.previousinputs: # Updating list 
            self.cachedinputs = list( set(glob) - self.previousinputs )
         else: # First pass
            self.cachedinputs = glob

         if not invalidateOnly:
            self.previousinputs = set(glob)

         # Randomize inputs.  Use nodename as lightweight seed guaranteed to be different on each node
         random.Random(options.name).shuffle(self.cachedinputs)


      if self.reduce:
         parts = [os.path.basename(i) for i in self.cachedinputs]
         parts = list(set(parts))  # Get unique partitions
         #print >>sys.stderr, "Cachedinputs", len(self.cachedinputs), "in", len(parts), "parts"
         putargs = "argv"
         if "-" in self.reduce:
            putargs = "stdin"

         for part in parts:
            #print >>sys.stderr, "PART", part
            # Don't process .d directories as named inputs (feedback loop)
            if part[-2:] == ".d":
               continue

            # Check to see if this node should proess this partition
            choices = list(Locations.pickn(part, n=1))

            if Locations.thisname not in choices:
                #print >>sys.stderr, Locations.thisname, "only hashes", part, "to", list(choices)
                continue

            #print >>sys.stderr, part, "processes on this node", list(choices)

            #Get list of files with this partition
            files = []
            remaininginputs = []
            for i in self.cachedinputs:
               if os.path.basename(i) == part:
                  files.append(i)
               else:
                  remaininginputs.append(i)

            # Remove these from the list of inputs to process later
            self.cachedinputs = remaininginputs

            outfilename = "/reduce/" + self.jobname + "/" + part + ".d"

            p = self.computeItem(files, outfilename, options, procs, invalidateOnly, steal=False, putargs=putargs)
            if p:
               #print >>sys.stderr, "Reduce part", part, "on node", Locations.thisname, files, "of", self.inputs
               return p

         return None # Nothing to do

      while self.cachedinputs or self.cachedinputs_deferred:
         # If we exhaust cachedinputs, fall-over to the deferred inputs
         if not self.cachedinputs:
            self.cachedinputs = self.cachedinputs_deferred
            self.cachedinputs_deferred = None # Keep track that we can't defer anymore

         i = self.cachedinputs.pop()

         if i[-2:] == ".d":
            # Don't process .d directories as named inputs (feedback loop)
            continue

         if i.startswith(options.rootdir):
            relativename = i[len(options.rootdir):]
         elif options.cowdir and i.startswith(options.cowdir):
            relativename = i[len(options.cowdir):]
         else:
            assert(not i)
            
         outfilename = relativename + ".d/" + escape(self.cmd)

         #TODO: steal if (self.cachedinputs_deferred == None) because there might be a slow node that we could beat.
         #But there's no point in doing this until we know how to later kill the slow node before it finishes.
         #steal = (self.cachedinputs_deferred == None)
         steal = False

         p = self.computeItem(i, outfilename, options, procs, invalidateOnly, steal)

         if p == 'defer' and False:
            self.cachedinputs_deferred.append(i)
         elif p:
            return p

      return None # Nothing to do

   def computeItem(self, inputs, outfilename, options, procs, invalidateOnly, steal, putargs="argv"):
      """Start (but don't wait for completion) running this job on of the next unprocessed input for this job."""
      if type(inputs) != type([]):
         inputs = [inputs]

      obase = options.rootdir + "/" + outfilename
      statfile = obase + "/" + ".status"

      # We invalidate outputs if inputs are newer, so find the newest input
      newestinput = 0
      for i in inputs:
         try:
            newestinput = max(newestinput, os.path.getmtime(i))
         except OSError:
            # Input no longer present, so we don't want to rerun
            return None

      # First check locally to see if output exists and is current
      try:
         lasttime = os.path.getmtime(statfile)
      except:
         lasttime = None

      if lasttime:
         if newestinput <= lasttime:
            #print >>sys.stderr, "Local results current for", statfile, self.checkexit
 
            if self.checkexit == None:
               return None

            try:
               stats = pickle.load(open(statfile, mode='rb'))
            except:
               print("Invalidating previous output based on unreadable stats file", statfile, file=sys.stderr)
            else:
               if stats['status'] != self.checkexit:
                  print("Invalidating previous output based on exit status", statfile, stats['status'], "instead of", self.checkexit, file=sys.stderr)
               else:
                  return None

         #Remove it now before somebody uses it for something
         dir = os.path.dirname(statfile)
         print("Removing stale results", dir, lasttime, newestinput, file=sys.stderr)
         parent = os.path.dirname(dir)
         dirname = os.path.basename(dir)

         tmp = parent + "/.del" + My_file_prefix + dirname
         print("Moving", dir, tmp, file=sys.stderr)
         try:
             os.rename(dir, tmp)
             shutil.rmtree(tmp)
         except OSError as e:
              if e.errno == errno.ENOENT:
                 # Somebody else just removed it, so let them have it
                 print("Looks like somebody else just removed %s, so skipping it" % (dir), file=sys.stderr)
                 return None
              else:
                 raise

         assert(not os.path.exists(statfile))
        
      #else:
      #   #print >>sys.stderr, "No local results", statfile

      # If we get here, then we're locally prepared to rerun
      # Check global synchronization to see if another node already ran it
      l = self.locker.start(outfilename, newestinput, exclusive=(not steal))

      if l == 'done':
          # Somebody already completed
          return None

      elif l == False:
          # Did not get (exclusive was specified and item is in progress elsewhere)
          assert(not steal)
          return 'defer'

      assert(l == True)

      # We are ready to start processing

      if invalidateOnly:
         # Don't actually do anything right now
         return None

      # Now we proceed to execute.
      # XXX. our scheduler should check and kill us off if somebody finishes first

      # Now insert a "." at the beginning of the basename for partial output
      odirname = os.path.dirname(obase)
      obasename = os.path.basename(obase)
      obase = odirname + "/." + My_file_prefix + "_" + obasename

      oname = obase + "/stdout"
      ename = obase + "/.stderr"
      if os.path.exists(obase):
         shutil.rmtree(obase)
      mkdirexist(obase)

      sout = os.fdopen(os.open(oname, os.O_CREAT|os.O_WRONLY|os.O_TRUNC), "w")
      serr = os.fdopen(os.open(ename, os.O_CREAT|os.O_WRONLY|os.O_TRUNC), "w")

      # Make a local copy of cmd so we can substitute this input file in it
      cmd = copy.copy(self.cmd)

      if putargs == "argv":
          subed = False
          for i, c in enumerate(cmd):
             if '%(input)' in c:
                cmd[i] = c.replace('%(input)', " ".join(inputs))
                subed = True
             if c == '|' and not subed:
                cmd[i:1] = inputs
                subed = True

          if not subed:
             cmd += inputs
      else:
          inputlist = "\n".join(inputs)

      i = 0
      while i < len(cmd):
         if cmd[i] == "fm" and (i == 0 or cmd[i-1] == "|"):
            cmd[i:i+1] = options.fmcmd
            i += len(options.fmcmd)
         else:
            i += 1

      cmd = [os.path.expanduser(c).encode('utf-8') for c in cmd]

      try:
         if putargs == "argv":
            p = procs.Popen(cmd, stdout=sout, stderr=serr, cwd=obase)
         if putargs == "stdin":
            p = procs.Popen(cmd, stdinstr=inputlist, stdout=sout, stderr=serr, cwd=obase)
      except:
         #print >>serr, "Error", sys.exc_value, "executing", cmd
         print("Error", sys.exc_info()[1], "executing", cmd, file=sys.stderr)
         raise

      assert(p)
      #print >>sys.stderr, "JOB RUNNING", self.jobname, p, procs.pids, inputs
      p.inputsize = 0
      p.inputs = inputs
      for i in inputs:
         p.inputsize += os.path.getsize(i)
      p.outdirname = odirname
      p.outbasename = obasename
      p.outrelpath = outfilename
      p.cmd = self.cmd
      p.jobname = self.jobname
      p.job = self
      self.running.append(p)

      sout.close()
      serr.close()

      #print >>sys.stderr, "computeItem", cmd, Hostname, p.pid
      return p

class CommandSetBase(object):
   """This is a base-class for defining methods which are used as
   command line-based commands.  You should inherit from it and define
   methods.  All methods will be callable.  Usage and help information
   will only include methods that do not begin with an underscore."""

   def __method(self, mname):
      return self.__class__.__dict__[mname]

   def _usage(self):
      """Return a multi-line usage string based on the defined methods and
their doc strings."""

      usage = 'For more help, specify one of the following commands followed by -h option:\n'
      keys = list(self.__class__.__dict__.keys())
      keys.sort()
      for cmd in keys:
         if cmd[0] == "_":
            continue
         method = self.__method(cmd)
         docstr = method.__doc__
         if docstr:
            docstr = docstr.split("\n")[0].strip().rstrip(".")
         usage += "   %-8s - %s\n" % (cmd, docstr)
      return usage

   def __init__(self, args, optParser=None):
      if not optParser:  
         optParser = MethodOptionParser()
         optParser.set_usage("""%prog command args...\n""" + self._usage())
      (options, args) = optParser.parse_args(args)
   
      if not args:
         optParser.print_help()
         sys.exit(1)

      try:
         method = self.__method(args[0])

      except:
         print("Unknown command", args[0], file=sys.stderr)
         optParser.print_help()
         sys.exit(1)

      sys.exit(method(self, args[1:]))

   def _optionHook(self, optParser):
      pass

   
class RedisSynchronizer:
    def __init__(self, locs):
        url = locs.this.syncdir
        import redis
        self.redis = redis.client.Redis.from_url(url)
        self.hostname = socket.gethostname()
        self.procs = locs.procs
        self.locs = locs

    def _canonicalize(self, pth):
        return pth.replace('//', '/').lstrip('/')

    def invalidate(self, lst):
        nonglobs = []
        lst = [self._canonicalize(l) for l in lst]
        
        for i in lst:
           if '*' in i:
              # We could explicitly register this so we can call it multiple times a little more efficiently (maybe)
              script = self.redis.register_script("local r = redis.call('keys', KEYS[1]); if table.getn(r) > 0 then redis.call('del', unpack(r)); end")
              script(keys=[i])
           else:
              nonglobs.append(i)

        if nonglobs:
           self.redis.delete(nonglobs)

    def start(self, filename, newestinput, exclusive):
        """Semantics here are complicated.  Grab this (and return True) if any of the following are true:
        0. Nobody has grabbed this yet
        1. Our newestinput is newer than the timestamp
        2. The node that claimed this before was us
        3. The node that claimed this before is now inactive
        4. Somebody else has started, is not us, is not inactive, is not finished, and exclusive==False

        If #4 is true, except that exclusive==True, then return 'defer'.
        In any other case, return False. 
        """

        filename = self._canonicalize(filename)
        
        value = self.locs.thisname + " " + str(newestinput)

        # First try at atomic test and set
        r = self.redis.setnx(filename, value)
        if r:
           # Got it exclusively
           return True

        # Failed the atomic, so see who claimed it and if we want to steal (node dead)
        #print >>sys.stderr, "REDIS GET", filename, r
        r = self.redis.get(filename)
        if r:
           r = r.split()
           if r[0] != self.locs.thisname and r[0] in self.locs.config.locs and not self.locs.config.locs[r[0]].inactive:
              if r[1] >= newestinput:
                 if len(r) == 3 and r[2] == ".":
                    return 'done'

                 if len(r) < 3 and exclusive:
                    return False

        self.redis.set(filename, value)
        return True
    
    def done(self, filename, timestamp):
        filename = self._canonicalize(filename)
        self.redis.set(filename, self.locs.thisname + " " + str(timestamp) + " .")
        
class FileSynchronizer:
    def __init__(self, locs):
        self.locs = locs
        self.syncdir = locs.this.syncdir

    def invalidate(self, lst):
        # Delete sync files so that computation is forced to (re-)execute
        # These files are shared, so we pick a minimum number of nodes to do this on
        syncfiles = [self._filename2lock(i) for i in lst]
        return self.locs.pick().forAllLocal(["localrm", "-R", "--absolute"]  + syncfiles)

    # We _desire_ near-atomicity on first to claim a job (since others will prefer to avoid duplication)
    #    race conditions should result in multiple holders rather than no holders
    # We don't worry so much about races between multiple finishers (any can win; they've already done the work),
    #    race conditions should result in multiple holders rather than no holders
    # but we want others testing for done-ness to promptly know if anybody has finished.
    # We also want to keep track of how many are in process so that we don't over-duplicate

    def start(self, filename, newestinput, exclusive):
        # Locally we want to (re-)create output. 
        # exclusive is True iff we want the first lock (not if anybody else has started)

        # Return 'done' if the status is complete
        # Return False if somebody else has started and exclusivity was requested
        # Return True if we should start (given the status and requested exclusivity)

        # Doing an atomic operation is expensive and we're really only worried about simultaneous creation,
        # so first just stat() to see if it file already exists.
        syncfilename = self._filename2lock(filename)

        take = False

        try:
           contents = open(syncfilename).read()
        except IOError as e:
           if e.errno == errno.ENOENT:
              # Nobody has claimed it yet, so we will
              take = True
           elif e.errno == errno.ESTALE:
              # Looks like NFS file got deleted after opening
              take = True
           else:
              raise

        if not take:
           # Check to see if we think we need to invalidate it.
           contents = contents.split()
           node = contents[0]

           try:
              if ((node != self.locs.thisname) 
                 # If we did it last time, then redo it now (start() is called iff we have newer inputs than outputs)
                 and (node in self.locs.config.locs)
                 # if the node that did it is no longer active 
                 and (not self.locs.config.locs[node].inactive)
                 # Somebody else did it, but we have newer inputs, so redo it
                 # XXX. this doesn't remove the output elsewhere so if we shuffle both, we may get the old input
                 # Hopefully if our input changed, their's will too.   If a node is offline while the input updates
                 # and comes back later, it eneds to invalidate its result.  Perhaps we should only redistribute
                 # things we have current locks for.  Hopefully rsync -u will get the newer file in the end.
                 and (newestinput <= os.path.getmtime(syncfilename))):
                    # If we get here, then we do NOT want to invalidate
                    if len(contents) > 1:
                       # This means the output is complete
                       return 'done'
                    else:
                       return (not exclusive)
      
           except OSError as e:
              if e.errno == errno.ENOENT:
                 # Somebody else just removed it, so let them have it
                 return (not exclusive)
              else:
                 raise
   
           # If we get here, then we are going to invalidate and take the lock.
           try:
              os.unlink(syncfilename)
           except OSError as e:
              if e.errno == errno.ENOENT:
                 # We may be racing with another process that is just ahead of us.  
                 # In that case, we may both unlink sucessfully and both restart the work.
                 # Somebody else unlinked (but hasn't re-created yet).  Let them have it
                 return (not exclusive)
              else:
                 raise

        if self._atomicCreate(syncfilename):
           # We were the first
           return True
        else:
           # This is unlikely, but somebody else must have just started
           return (not exclusive)


    def done(self, filename, timestamp):
        # XXX. Uses current time (as recorded by NFS server on file modification) instead of timestamp
        syncfilename = self._filename2lock(filename)
        try:
           os.unlink(syncfilename)
        except:
           # This should only happen if somebody else just finished too
           pass
        return self._atomicCreate(syncfilename, ' .')

    def _atomicCreate(self, lockfilename, contents=''):
        myname = lockfilename + "_" + My_file_prefix
        mkdirexist(os.path.dirname(lockfilename))

        syncfile = os.fdopen(os.open(myname, os.O_CREAT|os.O_SYNC|os.O_WRONLY), "w")
        syncfile.write(self.locs.thisname + contents)
        syncfile.close()

        success = False

        try:
            os.link(myname, lockfilename)
            success = True
        except OSError as e:
            if e.errno != errno.EEXIST:
                os.unlink(myname)
                raise
            # Otherwise, somebody just beat us to it -- let them have it

        # Get rid of private name for it, successful or not
        os.unlink(myname)
 
        return success
   
    def _filename2lock(self, filename):
        # This converts to an output directory path (that will contain .status, stdout, etc. files)
        # to a unique filename in the syncdir.  The path is mostly the same,
        # except since the syncdir is a single directory across all nodes


        # Consider a virtual directory structure like the following
        #    /data/<timestamp>.d/cmd
        # with numerous <timestamp> values stored across nodes.
        # If we recreate that hierarchy in a centralized place, we may
        # have more directory entries in /data than the system supports.

        # Thus, we convert each element in the path from /foo to /XX/YY/foo
        # Where XX/YY is based on a hash of foo.  This should divide directory
        # entries across a large number of parent directories.  Using a base64
        # alphabet for XX/YY, this should support clusters of up to 2^24 nodes
        # with intermediate directories containing no more than 4096 entries.

        # We convert that to:
        #    /data/XX/YY/<timestamp>.d/cmd 
        # to avoid running out of diretory entries in /data/ in the syncdir
        # Where XX and YY are derived from hash(<timestamp>.d)

        inpath = filename.replace("//", "/")
        inpath = inpath.strip('/')
        outpath = [self.syncdir]
        while inpath:
           if '/' in inpath:
              parent, inpath = inpath.split('/', 1)
           else:
              parent = inpath
              inpath = None

           if '*' in parent or '?' in parent:
              # Wildcards propagate to hash
              outpath.append('??')
              outpath.append('??')
           else:
              filenamehash = printableHash(parent)
              outpath.append(filenamehash[:2])
              outpath.append(filenamehash[2:4])

           outpath.append(parent)

        outpath.append('status')
        syncfilename = '/'.join(outpath)

        return syncfilename

def print_df_line(disk, size, available):
   fmt =  "%20s %10s %10s  %5s"
   if not disk:
      print(fmt % ("Filesystem", "Size ", "Free  ", "Usage"))
   else:
      if size:
         usage = (size-available) * 100.0 /size
      else:
         usage = -1

      print(fmt % (disk, bytecount2str(size), bytecount2str(available), "%d%%" % usage))

class FmCommands(CommandSetBase):
   def __init__(self, args):
      """FileMap is a file-based map-reduce system.  
You can think of it is parallel and distributed xargs or make.  
It features replicated storage and intermediate result caching.

http://mfisk.github.com/filemap
"""

      self._locs = None
      p = MethodOptionParser()
      p.set_usage("""fm command args...\n""" + self._usage())
      p.add_option("-v", "--verbose", action="count", help="Increase verbosity (can be used multiple times)")
      (options, args) = p.parse_args(args)

      if options.verbose:
         global Verbose
         Verbose += options.verbose

      CommandSetBase.__init__(self, args, p)

   def _Locations(self):
      if not self._locs:
         self._locs = FmLocations()

      return self._locs

   def partition(self, args):
      """Partition an input file.  Split an inputfile into n pieces.
      Specify a whitespace-delimited field with -f.  All lines with
      the same key will be placed in the same output file.  The -r
      option can be used to specify a Perl-compatible regular
      expression that matches the key.  If the regex contains a group,
      then what matches the group is the key; otherwise, the whole
      match is the key.

      If nways is greater than 0, output files are numbered 1 to n.
      If nways is 0, then files will be named for the values of the keys.

      If nways is set and no field or regex is specified, then lines
      are partitioned round-robin.  All output files are gzip
      compressed and created in the current directory.  Input files
      ending in .gz will automatically be decompressed.
      """
      p = MethodOptionParser()
      p.add_option("-n", "--nways", help="Number of output files to use (0 means each value will get its own file)")
      p.add_option("-r", "--regex", help="Regex that matches the key portion of input lines")
      p.add_option("-f", "--field", help="Use field # or range (numbered starting with 1).")
      p.add_option("-Z", "--no-compress", action="store_true", help="Do NOT compress output files")
      (options, args) = p.parse_args(args)

      infiles = args

      if options.nways == None:
         p.error("-n option required")

      options.nways = int(options.nways)
     
      if options.regex:
         options.regex = re.compile(options.regex)
 
      if options.field:
         if "-" in options.field:
            options.field = options.field.split("-")
            options.field = [int(i)-1 for i in options.field]
            options.field[1] += 1
         else:
            options.field = [int(options.field) - 1, int(options.field)]

      files = {}

      i = 0

      if not infiles:
         infiles = ["-"]

      for infile in infiles:
         if infile == "-":
            f = sys.stdin
         elif infile.endswith("gz"):
            f = gzip.GzipFile(infile)
         else:
            f = open(infile) 

         for line in f:
            if options.regex:
               key = options.regex.search(line)
               if key:
                  g = key.groups()
                  if len(g):
                     key = g[0]
                  else:
                     key = key.group(0)
               else:
                  print("Key not found in line:", line.rstrip(), file=sys.stderr)
            elif options.field:
               words= line.split()
               #print words[options.field[0]:options.field[1]]
               key = words[options.field[0]:options.field[1]]
  
            fname = None 
            if options.nways:
               if options.regex or options.field:
                  i = int(sha(str(key)).hexdigest(), 16) % options.nways
               else:
                  i = (i + 1) % options.nways

               if i not in files:
                  fname = str(i+1)
 
            else:
               i = ','.join(key)
               if i not in files:
                  fname = escape([i])

            if fname:
               if not options.no_compress:
                  files[i] = gzip.GzipFile(fname + ".gz", "w")
               else:
                  files[i] = open(fname, "w")
               
            files[i].write(line)
   
      for f in files.values(): f.close()

   def kill(self, args):
      """Kill a job."""
      p = MethodOptionParser()
      p.add_option('-s', '--sched', action='store_true', help="Kill all remote schedulers and their children", default=False)
      (options, args) = p.parse_args(args)

      args = ["/jobs/" + a for a in args]
      if args:
         self._Locations().forAll(["rm", "-f"], args).collect()
      if options.sched:
         self._Locations().forAllLocal(["kill"]).collect()

   def mv(self, args):
      """Rename files in the cloud"""
      (options, args) = MethodOptionParser(fixed=["src...", "dst"]).parse_args(args)
      dst = args[-1]
      each = args[:-1]
      if len(each) > 1: dst += "/"
 
      self._Locations().forAll(["mv"], each, dst, quote=False).collect()

   def mkdir(self, args, absolutes=[], asynchronous=False):
      """Make a directory (or directories) on all nodes.  
Has unix "mkdir -p" semantics."""
      (options, args) = MethodOptionParser(fixed=["dir..."]).parse_args(args)
      # Make sure destination exists
      p = self._Locations().forAll(["mkdir", "-p", "-m", "2775"] + absolutes, args, subst=True, glob=False)
      if not asynchronous:
         p.collect()

   def jobs(self, args):
      """Show all of the jobs still active."""
      (options, args) = MethodOptionParser(fixed=[]).parse_args(args)

      pkls = self._local_pickles(["localjobs"])
      jobs = {}
      for mx in pkls:
         for jname,j in iteritems(pkls[mx]):
            if not jobs.get(jname):
               jobs[jname] = j
               j.nodes = [mx]
            else:
               jobs[jname].nodes.append(mx)

      # Second pass to get stats for all jobs (even on nodes that didn't have the job running)
      for j in jobs.values():
         statglobs = [i + ".d/" + escape(j.cmd) + "/.status" for i in j.inputs.split()]
         j.stats = list(itertools.chain(*list(self._local_pickles(["localstats"] + statglobs).values())))

      first = True

      for jname,j in iteritems(jobs):
         inputlist = j.inputs.split()
         flags = ""
         if j.reduce:
            flags = j.reduce + " "

         if not first:
            print()
         print(jname + "\t" + j.uid + "\t" + pipes.quote(flags + ' '.join(j.cmd)))
         flags = ""
         if j.continuous:
            flags += "-c "
         if j.checkexit != 0:
            flags += "-e "
        
         print("\t%s-i '%s'" % (flags, "' -i '".join(inputlist)))

         nodestr = ''
         if len(j.nodes) < 10:
            j.nodes.sort(cmp=numcmp)
            nodestr = ': ' + (','.join(j.nodes))
         print("\t%d nodes still processing%s" % (len(j.nodes), nodestr))

         self._tallyStats(j.stats, inputlist, indent='\t')
         first = False
      
   def df(self, args):
      """Show free space on each node."""
      (options, args) = MethodOptionParser(fixed=[]).parse_args(args)
      dfs = self._local_pickles(["df"])

      disks = []
      for mx in dfs:
         for d in dfs[mx]:
            size, available = dfs[mx][d]
            # Really only 1 disk per node, so just use node name
            disks.append((mx, size, available))

      # Sort by available, reversed
      disks.sort(lambda a,b: cmp(b[2], a[2]))
      print_df_line(None, None, None) #Defaults to header
      for d in disks:
            print_df_line(*d)
      
      print_df_line(None, None, None) #Defaults to header
      print_df_line("Total (%d disks)" % len(disks), 
                    sum([i[1] for i in disks]),
                    sum([i[2] for i in disks]))
               
   def loadavg(self, args):
      """Show load average."""
      (options, args) = MethodOptionParser(fixed=[]).parse_args(args)
      pkls = self._local_pickles(["localload"], unique_hosts=True)
      loadtotal = [0,0,0]
      cpus = 0
      for mx in pkls:
          loadtotal[0] += float(pkls[mx]['loadavg'][0])
          loadtotal[1] += float(pkls[mx]['loadavg'][1])
          loadtotal[2] += float(pkls[mx]['loadavg'][2])
          cpus += pkls[mx]['cpus']
          #print pkls[mx]
      print("Total load average: %.2f (%d%%) %.2f %.2f" % (loadtotal[0], 100.0 * loadtotal[0] / cpus, loadtotal[1], loadtotal[2]))

   def chmod(self, args, absolutes=[], ignoreErrors=False):
      """Change permissions on files in the cloud."""
      (options, args) = MethodOptionParser(fixed=["mode", "files..."]).parse_args(args)
      self._Locations().forAll(["chmod", args[0]] + absolutes, args[1:], subst=True, quote=False).collect(ignoreErrors=ignoreErrors)

   def chgrp(self, args, absolutes=[]):
      """Change GID on files in the cloud."""
      (options, args) = MethodOptionParser(fixed=["perm", "files..."]).parse_args(args)
      self._Locations().forAll(["chgrp", args[0]] + absolutes, args[1:], subst=True, quote=False).collect()

   def store(self, args):
      """Store one or more files into the cloud."""

      """src... dst

Copy the specified file(s) into the virtual store.  
"""
      p = MethodOptionParser(fixed=["files...", "dst"])
      p.add_option('-s', '--serialize', action='store', help="Number of nodes to store to concurrently", default=False, type=int)
      (options, args) = p.parse_args(args)

      dst = args[-1]
      args = args[:-1]

      args = multiglob(args)

      if len(args) > 1:
         dst += "/"

      replargs = [dst + os.path.basename(i) for i in args] 

      failover = 3
      while failover:
         # store to a single location first (then replicate)
         errors, results = self._Locations().put(args, dst, pickn=1, serialize=options.serialize).collect(markInactive=self._Locations().config)
         if not errors:
            break
         failover -= 1

      self.replicate(replargs)

   def _putJobs(self, tmpdir, maxErrors):
      self._Locations().put([tmpdir + "*"], "/jobs/").collect(maxErrors=maxErrors, markInactive=self._Locations().config)
      shutil.rmtree(tmpdir)

   def map(self, args):
      """Launch a computation on a set of input files in the cloud.
Run the specified command on each input file (in the virtual store)
described by the inputglob.  Multiple inputglob arguments can be
given.  The -c option says that the commond should continue to run on
new inputs as they arrive.

Multiple commands can be chained together with |.  Each output file of
the first command becomes an input for the next command in the
pipeline.

The -f option says that any previously cached output should be ignored
and the program re-run.
"""

      p = MethodOptionParser(fixed=["cmd [| cmd...]"])
      p.add_option("-i", "--inputglob", action="append", help="Glob of input files (in root)")
      p.add_option("-c", "--continuous", action="store_true", help="Continue to look for new input files to arrive")
      p.add_option("-f", "--fresh", action="store_true", help="Do not use any cached output")
      p.add_option("-q", "--quiet", action="count", help="Do not fetch and display stdout (or stderr if -qq)")
      p.add_option("-o", "--optimistic", action="store_true", help="Try to run even if there are many failures submitting job")
      p.add_option("-p", "--procspercpu", action="store", help="Number of processes to run per CPU (default=1)", default=1)
      p.add_option("-s", "--statusonly", action="store_true", help="Don't wait for completion; fetch any available results now")
      p.add_option("-e", "--checkexit", action="store_false", default=True, help="Do NOT stop on error or remove output from any previous run that had a non-zero exit status")
      p.add_option("-m", "--mail", action="store_true", help="E-mail results")
      p.add_option("-x", "--mx", action="store", help="SMTP server")
      (options, cmd) = p.parse_args(args)

      if not options.inputglob:
         p.error("-i or --inputglob must be specified")

      options.inputglob = set(options.inputglob)

      if "-" in options.inputglob:
         options.inputglob.update([l.strip() for l in sys.stdin])
         options.inputglob.remove("-")

      options.inputglob = list(options.inputglob)
      options.inputglob.sort()

      fresh = options.fresh # options.fresh gets rewritten later

      cmdwords = shlex.split(''.join(cmd))
      cmd = ' '.join(cmdwords)
      cmds = []
      # parse/replace pipe and reduce operators         
      # < redistribute
      # > reduce (inputs on argv, presumed composable)
      # >- reduce (inputs on stdin)
      # Can be composed such as ">.<>." which reduces locally, redistributes, then reduces again

      # The scheduler looks for reduce operations with the substrings:
      #   "stdin" which signifies to pass inputs on stdin rather than argv and 
      #   "part" which signifies to only reduce inputs who are in a partition owned by this node (which is what you do after a redistribute).


      # First split ><... and <>... into two tokens
      i=0
      while i < len(cmdwords):
         if cmdwords[i].startswith("><"):
            cmdwords.insert(i+1, cmdwords[i][1:])
            cmdwords[i] = cmdwords[i][0]

         if cmdwords[i].startswith("<>"):
            cmdwords.insert(i+1, cmdwords[i][1:])
            cmdwords[i] = cmdwords[i][0]
         i += 1

      #print >>sys.stderr, "cmdwords:", cmdwords

      # Then split-up into pipeline elements (separated by a word that starts with [|<>.]+ word)
      pipeline = [[]]
      while cmdwords:
         w = cmdwords.pop(0)
         if w in ["||", ">", "<", ">-"]:
            # Make a new pipeline element
            pipeline.append([])
         if w != "||":
            pipeline[len(pipeline)-1].append(w)
      if pipeline[0] == []:
         pipeline.pop(0)

      #print >>sys.stderr, "Pipeline:", pipeline

      # Duplicate cmd when there are multiple reduces
      i = 0
      while i < len(pipeline):
            if pipeline[i][0].startswith(">") and (len(pipeline[i]) == 1):
               # Copy reduce command and modifier from next pipeline element
               if i+2 >= len(pipeline) or pipeline[i+1][0] != "<":
                  print("Cannot parse command ending in >", file=sys.stderr)
                  return False

               pipeline[i][1:] = pipeline[i+2][1:]
               if pipeline[i+2][0].endswith("-"):
                  pipeline[i][0] += "-"

            if pipeline[i][0] == "<" and len(pipeline) > i+1:
               pipeline[i+1][0] += "part"

            i += 1

      #print >>sys.stderr, "Pipeline2:", pipeline

      if options.mail:
         import smtplib
         import socket
         import email.mime.multipart
         import email.mime.image
         import email.mime.text
         import email.mime.base
         import email.encoders

         user = pwd.getpwuid(os.getuid()).pw_name
         host = socket.getfqdn()
         domain = '.'.join(host.split('.')[1:])

         if options.mx:
            mx = options.mx
         else:
            try:
               import dns.resolver
               mx = dns.resolver.query(domain, 'MX')[0]
               mx = str(mx.exchange)
            except:
               mx = "mail"

         # If we couldn't get a good FQDN from the default interface,
         # try again on the interface used to talk to the MX
         if not domain or domain == "localdomain":
            # Try on an actual socket to the mx
            s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
            try:
               s.connect((mx, 25))
            except:
               print("Could not connect to mail exchanger '%s'" % mx, file=sys.stderr)
               return 1

            host = socket.gethostbyaddr(s.getsockname()[0])[0]
            domain = '.'.join(host.split('.')[1:])

            s.close() 

         fromaddr = '@'.join([user,host])
         toaddr = '@'.join([user,domain])

         print("Results will be in mail from %s to %s via %s" % (fromaddr, toaddr, mx))

         msg = email.mime.multipart.MIMEMultipart()
         msg['Subject'] = "Filemap results for '%s'" % ("' '".join(args))
         msg['From'] = fromaddr
         msg['To'] = toaddr

         stdout = io.BytesIO()
         realstderr = sys.stderr
         sys.stdout = stdout
         sys.stderr = stdout

      try:
         finished = self._domap(options, pipeline)

         if options.mail:
            output = ""
            for line in stdout.getvalue().split("\n"):
               #if len(line) > 500:
                   #line = line[:500] + "..."
               output += line + "\n"
            msg.attach(email.mime.text.MIMEText('<pre>' + output + '</pre>', 'html'))

            sys.stderr = realstderr
            sys.stdout = realstderr
   
            if finished:
               imgfile = io.BytesIO()

               obj = email.mime.base.MIMEBase('application','octet-stream')
               obj.set_payload(open(".fm.stats.gz").read())
               email.encoders.encode_base64(obj)
               obj.add_header('Content-Disposition', 'attachment', filename="fm.stats.gz")
               msg.attach(obj)

               try:
                  self.plot([".fm.stats.gz", imgfile])
                  img = email.mime.image.MIMEImage(imgfile.getvalue())
                  img.add_header('Content-Disposition', 'inline', filename="fmstats.png")
                  msg.attach(img)

               except:
                  print("Unable to generate plot:", file=sys.stderr)
                  traceback.print_exc(limit=0)
      
            # Send the email via our own SMTP server.
            s = smtplib.SMTP(mx)
            s.sendmail(fromaddr, toaddr, msg.as_string())
            s.quit()

      except:
         if options.mail:
            sys.stderr = realstderr
            print(stdout.getvalue(), file=realstderr)

         raise

      return None
   

   def _domap(self, options, pipeline):
      if options.statusonly:
         tmpdir = None
      else:
         tmpdir = mkdtemp(prefix="map") + "/"

      inglobs = options.inputglob
      allinglobs = set(inglobs)
      outdirglobs = []
      statglobs = []
      assert (type(inglobs) == type([]))
      starttime = None
      jobname = None
      joblist = []

      if options.optimistic:
         maxErrors = None
      else:
         maxErrors = 0
         # If replicate uses pickn=True, then use self._Locations().this.replication-1 here
         # since pickn defaults to false, to default to no errors allowed

      for cmd in pipeline:
         reduce = False

         # Global barrier 
         if cmd[0] == "<" or cmd[0][0] == ">":
            if jobname and not options.statusonly:
               # Install the jobs on each node
               self._putJobs(tmpdir, None)

            if not options.statusonly:
               tmpdir = mkdtemp(prefix="map") + "/"

            if not starttime:
               starttime = time.time()

            if not options.statusonly:
               if jobname:
                  args = ["wait", jobname]
                  jobname = None # This won't be a parent of the first thing after the barrier
               else:
                  args = []

               if cmd[0] == "<":
                  args += ["redistribute"] + inglobs

               if args:
                  # Barrier; Wait for that job (and its parents) to finish:
                  if Verbose > -1:
                     print("Waiting for %s" % ' '.join(args), file=sys.stderr)

                  r = self._Locations().forAllLocal(args).collect(maxErrors=maxErrors, stopOnError=True)
                  if not r:
                     #Kill job since we returned early with an error
                     self.kill(joblist)
                     return False
               #else beginning of pipeline, or just had a barrier, so nothing to wait on

            if cmd[0] == "<":
               continue
            # else reduce and we need to do the reduce job now

         # Look for reduce operations
         if cmd[0][0] == ">":
            reduce = cmd[0]
            cmd = cmd[1:]
      
         allinglobs.update(inglobs)
         jobname, inglobs = self._MapComponent(cmd, inglobs, outdirglobs, options, reduce=reduce, parent=jobname, tmpdir=tmpdir, procsPerCpu = int(options.procspercpu), checkexit=options.checkexit)
         joblist.append(jobname)

      if not options.statusonly:
         # Install the jobs on each node
         self._putJobs(tmpdir, None)

      if not starttime:
         starttime = time.time()

      if not options.statusonly:
         if Verbose > -1:
            print("Waiting for completion.  Job", jobname, file=sys.stderr)
         r = self._Locations().forAllLocal(["wait", jobname]).collect(maxErrors=maxErrors, stopOnError=True)
         if not r:
            #Kill job since we returned early with an error
            self.kill(joblist)
            return False
         wallclock = time.time() - starttime
      else:
         wallclock = None

      # Get the output files
      errglobs = [f + "/.stderr" for f in outdirglobs]
      statglobs += [f + "/.status" for f in outdirglobs]
      if Verbose > -1:
         print("Output in:\n\t", "\n\t".join(outdirglobs), file=sys.stderr)

      statlists = self._local_pickles(["localstats"] + statglobs)
      allstats = list(itertools.chain(*list(statlists.values())))

      if options.statusonly:
         tally_start = None
      else:
         tally_start = starttime

      tally = self._tallyStats(allstats, allinglobs, tally_start, wallclock)
      statsfile = gzip.GzipFile('.fm.stats.gz', 'w')
      pickle.dump(allstats, statsfile)
      statsfile.close()

      # Fetch stdout/stderr               
      if not options.quiet or options.quiet < 2:
         if options.quiet or options.statusonly:
            outputglobs = []
         else:
            outputglobs = inglobs

         self.get(["-ce"] + outputglobs + errglobs, relative=True)

      return True

   def _tallyStats(self, statlist, inputglobs, starttime=None, wallclock=None, indent=''):
      nodecount = self._Locations().processes()

      # Tally the stats
      errcodes = {}
      wtime = [0.0, 0.0]
      utime = [0.0, 0.0]
      stime = [0.0, 0.0]
      bytes = [0, 0]
      nodewtime = [{}, {}]
      nodebytes = [{}, {}] 
      allstats = []
      maxend = 0
      if not starttime:
         starttime = time.time()

      minstart = starttime

      for stats in statlist:
            ec = os.WEXITSTATUS(stats['status'])
            errcodes[ec] = errcodes.get(ec, 0) + 1

            if stats['timestamp'] < starttime:
               cached = 1
            else:
               cached = 0

            wtime[cached] += stats['time']
            utime[cached] += stats['utime']
            stime[cached] += stats['stime']
            bytes[cached] += stats['inputsize']

            minstart = min(minstart, stats['start'])
            maxend = max(maxend, stats['timestamp'])

            nodename = stats['nodename']
            nodewtime[cached][nodename] = nodewtime[cached].get(nodename, 0) + stats['time']
            nodebytes[cached][nodename] = nodebytes[cached].get(nodename, 0) + stats['inputsize']

      # Print out summary info
      errstr = ''
      for k in errcodes.keys():
         if not errstr:
            errstr = "%d processes returned %d" % (errcodes[k], k)
         else:
            errstr += "; %d x %s" % (errcodes[k], k)
      if not errstr:
         errstr = '0 processes completed'

      print(indent+errstr, file=sys.stderr)

      if Verbose > 0:
         for n in nodebytes[0]:
            if nodewtime[0][n]:
               print(indent+"Node %s %s/s new work" % (n, bytecount2str(nodebytes[0][n]/nodewtime[0][n])), file=sys.stderr)

      swtime = sum(wtime)

      if swtime:
         sbytes = sum(bytes)
         sutime = sum(utime)
         sstime = sum(stime)
         print(indent+"Serial performance: %s, %s/s, %s (%.0f%% User, %.0f%% System, %.0f%% Wait)" \
            % (bytecount2str(sbytes), bytecount2str(sbytes/swtime), seconds2human(swtime), 100*sutime/swtime, 100*sstime/swtime, 100*(swtime-sstime-sutime)/swtime), file=sys.stderr)

         if bytes[0] and wallclock:
            rate = bytecount2str(bytes[0]/wallclock)
            scaling = (stime[0]+utime[0])/wallclock
            print(indent+"New: %s/s, %.1f/%dx scaling." % (rate, scaling, nodecount), file=sys.stderr)
         
         # Find intervals we were computing over 
         intervals = [(s['start'], s['timestamp']) for s in statlist]
         intervals = collapseIntervals(intervals)

         if bytes[1]:
            # Find intervals that were before starttime (cached)
            cacheduration = 0
            for (start,end) in intervals:
               if end < starttime:
                  cacheduration += (end-start)

            if cacheduration:
               rate = bytecount2str(bytes[1]/cacheduration)
               scaling = swtime/cacheduration
               print(indent+"Cached: %s/s, %s, %.1fx" % (rate, seconds2human(cacheduration), scaling), file=sys.stderr)

         if sbytes and wallclock:
            rate = bytecount2str(sbytes/wallclock)
            cached = 100*bytes[1]/sbytes
            print(indent+"Overall: %s/s, %s, %.0f%% cached." % (rate, seconds2human(wallclock), cached), file=sys.stderr)
  
      if not wallclock:
         wallclock = maxend - minstart
         #print >>sys.stderr, "Estimated wallclock time:", seconds2human(wallclock)

      # Report percent complete
      if wallclock and swtime:
         ls = self._lsdict(list(inputglobs))
         totalsize = 0
         for f in ls.keys():
            totalsize += min([i['size'] for i in ls[f]])
     
         if totalsize:
            #print sbytes, totalsize, totalsize-sbytes
            print(indent+"%d%% complete, %s remaining" % (100.0*sbytes/totalsize, seconds2human(wallclock/(1.0*sbytes/totalsize) - wallclock)), file=sys.stderr)

   def get(self, *args, **kwargs):
      """Copy one or more files from the cloud to local storage."""
      self._Locations().get(*args, **kwargs)

   def replicate(self, args):
      """Replicate the specified files in the virtual filesystem to the correct set of 
nodes.

Use this command after adding or removing nodes in the cluster in order to make
sure that each specified file is replicated on the correct set and number of 
nodes.  Upon successful replication, any excess copies are also removed.
      """
      (options, args) = MethodOptionParser(fixed=["files.."]).parse_args(args)

      self._Locations().forAllLocal(["replicate"] + args).collect(labelPrint=True)

   def run(self, args):
      """Run a command on each node and print results."""
      (options, args) = MethodOptionParser(fixed=["cmd..."]).parse_args(args)
  
      self._Locations().forAll(args, subst=True, quote=False).collect(labelPrint=True)

   def runhost(self, args):
      """Run a command on each unique host and print results."""
      (options, args) = MethodOptionParser(fixed=["cmd..."]).parse_args(args)
       

      self._Locations().pickHosts().forAll(args, quote=False).collect(labelPrint=True)

   def cat(self, args):
      """Concatenate one or more files to stdout.  
Unlike 'get -c', duplicate instances of files will be included."""
      (options, args) = MethodOptionParser(fixed=["files..."]).parse_args(args)

      (pcount, rprocs) = self._Locations().pickHosts().forAll(["cat"], args).collect(ignoreErrors=True)

      for f in rprocs:
         sys.stdout.writelines(f.stdout)

   def plot(self, args):
      """Plot run-time of a previous map."""
      p = MethodOptionParser(fixed=["[infile [outfile]]"])
      p.add_option("-r", "--redundant", action="store_true", default=False, help="report redundant work")
      p.add_option("-g", "--group-host", action="store_true", default=False, help="group nodes by host")
      (options, args) = p.parse_args(args)
      infile = ".fm.stats.gz"
      pngfile = "fmstats.png"

      if args:
         infile = args[0]
      else:
         print("Using %s as default input file" % infile, file=sys.stderr)
   
      if len(args) > 1:
         pngfile = args[1]
      else:
         print("Using %s as default output file" % pngfile, file=sys.stderr)
   
      if len(args) > 2:
         print("Usage: fm plot [<infile> [<outfile>]]", file=sys.stderr)
         sys.exit(-1)

      if type(infile) == type(''):
         infile = gzip.GzipFile(infile)
   
      plot(infile, pngfile, options)

   def _local(self, args):
      """This is for slave (remote) instantiations."""
      return FmLocalCommands(args)

   def _local_pickles(self, args, unique_hosts=False):
      """Execute a command on each node and return a dict of the unpickled output from each node (node->output)."""

      locs = self._Locations()
      
      if unique_hosts:
         locs = locs.pickHosts()

      procs = locs.forAllLocal(args)
      status, ps = procs.collect()

      pickles = {}

      for p in ps:
         pkl = p.stdout.read()
         p.stdout.close()
         if not pkl:
            continue

         try:
            unpkl = pickle.loads(pkl)
         except:
            print("Error", sys.exc_info()[1], "parsing remote pickle results:", pkl, file=sys.stderr)
            return 1   # TODO: this value isn't ever expected/handled by the code calling this function
                       # we should return an empty list or check the list contents or at least the
                       # return type after this function is called
         pickles[p.queue] = unpkl

      return pickles

   def _ls(self, args):
      """generic way to get info about files in a blob"""             
      if not args:
         args = ["/"]
      pkls = self._local_pickles(["localls"] + args)

      listing = {}

      for nodename in pkls:
         for f in pkls[nodename]:
            fname = f['name']
            f['nodename'] = nodename
            dictListAppend(listing, fname, f)

      return listing

   def fs(self, args):
      p = MethodOptionParser(fixed=["<dir>..."])
      p.add_option('-r', '--replication', action='store', help="Replication level to check for", default=self._Locations().this.replication)
      p.add_option('-f', '--fix', action='store_true', help="Fix file system")
      p.add_option('-v', '--verbose', action="count", help="Up verbostiy, more occurrances means higher level")
      p.add_option('-d', '--dryrun', action='store_true', help="Display proposed fix, do not execute")
      (options, args) = p.parse_args(args)

      options.replication = int(options.replication)

      listing = self._ls(args)

      toofew = set()
      toomany = set()
      total = len(list(listing.keys()))

      for i in listing.keys():
         if len(listing[i]) < options.replication:
            toofew.add(i)
         if len(listing[i]) > options.replication:
            toomany.add(i)

      print(total, "files found")
      print(len(toofew), "files don't have enough replication")
      print(len(toomany), "files have too much replication")
      print(total - len(toofew) - len(toomany), "files' replication is just right")

      if options.dryrun:
         print("Need to up replication on:")
         print(toofew)
         print("Need to prune replication on:")
         print(toomany)
         sys.exit(0)

      if options.fix:
         pass
         # for i in too few, find differnece in replication and occurrences, select hosts to store
         # for i in too many, find differnece in replication and occurrences, select hosts to remove

   def _lsdict(self, args, decode=False):
      ls = {}
      listing = self._ls(args)

      for fkey in listing.keys():
         if decode:
            (fname, num) = quoprire.subn(lsUnescapeChr, fkey)
         else:
            fname = fkey

         ls[fname] = listing[fkey]

      return ls
       
   def ls(self, args):
      """File & directory listing."""
      p = MethodOptionParser(fixed=["[files...]"])
      p.add_option('-n', '--nodes', action='store_true', help="List names of nodes holding each file")
      p.add_option('-l', '--long', action='store_true', help="Show permissions, nodes, sizes, timestamps, etc.")
      p.add_option('-q', '--decode', action='store_true', help="Replace escaped characters")
      p.add_option('-1', '--single', action='store_true', help="Single-column output")
      (options, args) = p.parse_args(args)

      ls = self._lsdict(args, options.decode)

      fnames = list(ls.keys())
      fnames.sort()

      if not options.long:
         if options.single:
            for f in fnames: print(f)
         else:
            tabulate(fnames, int(os.environ.get("COLUMNS", 80)))

      else:
         totalsize = 0
         for f in fnames:
            for i in range(len(ls[f])):
               if not ls[f][i]:
                  continue

               # This is the cumulative attributes combined from multiple nodes
               attrs = ls[f][i]
               attrs['mtime'] = list([attrs['mtime']])
               attrs['user'] = set([attrs['user']])

               # If you specify the same file twice, we don't want
               # the node number(s) duplicated in the node list, so make it a set
               nodes = set([attrs['nodename']])

               isdir = (attrs['perms'][0] == 'd')
               islnk = (attrs['perms'][0] == 'l')
               criteria = ['perms', 'group']
               if isdir:
                  attrs['size'] = 0
               else:
                  criteria.append('size')
           
               # Look for duplicates from other nodes later in the list
               for j in range(i+1, len(ls[f])):
                  if not ls[f][j]:
                     continue
   
                  # See if this node's instance matches the right criteria to be
                  # collapsed into a single output line
                  match = True
                  for a in criteria:
                     if attrs[a] != ls[f][j][a]:
                        # Does not match
                        match = False
                        break
   
                  if match:
                     nodes.add(ls[f][j]['nodename'])
                     attrs['mtime'].append(ls[f][j]['mtime'])
                     attrs['user'].add(ls[f][j]['user'])
                     ls[f][j] = None
   
               # Update the nodelist for this attrs instance
               nodes = list(nodes)
               nodes.sort(cmp=numcmp)
               attrs['nodename'] = nodes
   
               # Print out this file
               print(self._lsline(attrs, f, listnodes=options.nodes))

            # Sum up unique sizes (don't mutliply-count identical replicas)
            totalsize += sum(list(set([i['size'] for i in ls[f] if i])))

         print("%s" % bytecount2str(totalsize))
      return 

   def _timemask(self, mtimes):
      # Find common time string across all instances
      times = [time.strftime("%Y %b %d %H %M", time.localtime(t)).split() for t in mtimes]

      common = []
      for i in range(5):
          vec = list(set([t[i] for t in times]))
          if len(vec) > 1:
              common.append('-')
          else:
              common.append(vec[0])

      # See if it was this year or not
      if common[0] != '-' and int(common[0]) == time.localtime()[0]:
         return "%3s %2s %2s:%2s" % (common[1], common[2], common[3], common[4])
      else:
         return "%3s %2s  %4s" % (common[1], common[2], common[0])

   def _lsline(self, attrs, name, listnodes=False):
      if not int:
         return attrs['name']

      size = "%-.2g" % attrs['size']
      size = size.replace("e+", "e").replace("e0", "e")

      nodes = attrs['nodename']
      if type(nodes) != type([]):
         nodes = [nodes]

      if len(nodes) != len(attrs['mtime']):
         print(nodes, attrs['mtime'])

      attrs['mtime'] = self._timemask(attrs['mtime'])

      if len(attrs['user']) == 1:
         attrs['user'] = attrs['user'].pop()
      else:
         attrs['user'] = '*'

      if listnodes:
         if len(nodes) == len(self._Locations().config.locs):
            nodes = '*'
         else:
            nodes.sort(cmp=numcmp)
            nodes = ','.join(nodes)
      else:
         nodes = len(nodes)

      return "%s %7s %8s %8s %6s %12s %s" % (attrs['perms'], nodes, attrs['user'], attrs['group'], size, attrs['mtime'], name)

   def rm(self, args):
      """Delete a file or directory tree in the cloud.
Remove empty file or directory.  Normal rm flags are passed through; -f is implied.
"""
      p = MethodOptionParser(fixed=["files..."])
      p.add_option('-R', '--recurse', action='store_true', help="recurse")
      (options, args) = p.parse_args(args)
      if options.recurse:
         options = ["-R"]
         children = [a + "/*" for a in args]
      else:
         options = []
         children = []

      self._Locations().forAllLocal(["localrm"] + options + args).collect()

      # Now clean-up the syncdir 
      r = self._Locations().locker.invalidate(args + children)
      if r:
         r.collect()

   def init(self, args):
      """Create/correct directory structure.
 If a groupname is specified, it will be applied to the directories."""
      (options, args) = MethodOptionParser(fixed=["[group]"]).parse_args(args)

      if self._Locations().this.syncdir.startswith("redis:"):
         absolutes=[]
      else:
         absolutes=["%(SYNCDIR)"]
         
      self.mkdir(["/", "/jobs", "/reduce", "/sys"], absolutes=absolutes, asynchronous=True)
      if args:
         self.chgrp([args[0], "/", "/jobs", "/reduce", "/sys"], absolutes=absolutes)
      self.chmod(["g+rwxs", "/", "/jobs", "/reduce"], absolutes=absolutes, ignoreErrors=True)
      self._Locations().put([os.path.realpath(__file__)], "/sys/").collect()


   def _MapComponent(self, cmd, inglobs, outglobs, options, reduce=False, parent=None, tmpdir="/tmp/", procsPerCpu=None, checkexit=False):
      jobdesc = "[mrjob]\ncmd = %s\ninputs = %s\n" % (repr(cmd), ' '.join(inglobs))
      if parent:
         jobdesc += "parent = %s\n" % (parent)

      if procsPerCpu:
         jobdesc += "procspercpu = %s\n" % (procsPerCpu)

      if options.continuous:
         jobdesc += "continuous = True\n"

      if reduce:
         jobdesc += "reduce = %s\n" % (reduce)

      if checkexit:
         jobdesc += "checkexit = 0\n"

      h = printableHash(jobdesc)

      if options.statusonly:
         # Even if the user cut & pasted a -f flag, it never makes since to honor it with -s
         options.fresh = False
      else:
         jobfilename = tmpdir + h
         jobfile = open(jobfilename, "w")
         jobfile.write(jobdesc)
         jobfile.close()
   
      # Each component of pipeline uses previous output as input
      if reduce:
         newinglobs = ["/reduce/" + h + "/*"]
         outglobs += newinglobs
      else:
         newinglobs = [i + ".d/" + escape(cmd) for i in inglobs]
         outglobs += newinglobs

      if options.fresh:
         #XXX lower latency to accumulate these up to map() and let it do a bulk delete

         if reduce:
            p = self._Locations().locker.invalidate(['/reduce/' + h + '/*'])
         else:
            p = self._Locations().locker.invalidate([g + ".d/" + escape(cmd) for g in inglobs])

         if p:
            p.collect()

         # Also delete previous output so that it doesn't keep getting used
         # (In the case of replication, a node may not replace the old output with new output
         #self._Locations().forAllLocal(["localrm"] + newinglobs).collect()
         self.rm(["-R"] + newinglobs)

         # Only force the first stage of the pipeline.  Out-of-date checks will handle downstream.
         options.fresh = False

      newinglobs = [i + "/*" for i in newinglobs]
      return h, newinglobs

class SchedLock:
   """Traditional daemon-style lock as a file containing the pid of the holder"""
   def __init__(self, rootdir):
      self.lockname = rootdir + "/.fmschedlock-" + str(os.getuid())

   def kill(self):
      pid = open(self.lockname).read()
      os.kill(int(pid), signal.SIGTERM)
  
   def checkpid(self):
      # Check for running
      try:
         f = open(self.lockname)
      except:
         return False

      pid = f.read().strip()
      if not pid:
         print("Warning, ignoring empty lockfile", self.lockname, file=sys.stderr)
         return False
      pid = int(pid)

      try:
          # This will do nothing, but make sure the proc is running and ours
          os.kill(pid, 0)

          # If we got here, then the process exists, so give up
          return pid
      except OSError as e:
          if e.errno == errno.ESRCH:
             # process not running
             return None

          if e.errno == 1:
             # some linux systems now returning a permission error  if pid not exists!
             if os.path.isdir("/proc/%d" % pid):
                return None

          # Some other unexpected error
          raise
      
   def lock(self):
      # Check for running
      if self.checkpid():
         return False
      else:
         # Stale or empty, so steal.  
         # XXX race here if 2 procs competing to steal and 1 unlinks and recreates before 2nd unlinks
         tmp = self.lockname + "_" + My_file_prefix
         try:
            os.unlink(self.lockname)
         except:
            pass
         
         f = open(tmp, "w")
         f.write(str(os.getpid()))
         f.close()
         try:
            os.rename(tmp, self.lockname)
         except OSError as e:
            if e.errno == errno.EEXIST:
               # Somebody beat us
               return False
            else:
               raise

      os.setpgrp()  # create new process group, become its leader
      signal.signal(signal.SIGTERM, killProcessGroup)

      return True

   def unlock(self):
      #XXX: doesn't check that we still hold the lock
      os.unlink(self.lockname)

def killProcessGroup(signum, frame):
   os.kill(0, signal.SIGTERM)
   sys.exit(1)

def setProcessName(name):
   try:
      import ctypes
      libc = ctypes.cdll.LoadLibrary('libc.so.6')
      buf = ctypes.create_string_buffer(len(name)+1)
      buf.value = name
      libc.prctl(15, ctypes.byref(buf), 0,0,0)

   except:
   #   print >>sys.stderr, "Unable to set process name:"
   #   traceback.print_exc()
      pass
      
class FmLocalCommands(CommandSetBase):
   def __init__(self, args):
      self._locs = None
      p = MethodOptionParser()
      p.set_usage("""fm _local command args...\n""" + self._usage())
      p.add_option("-n", "--node", action='append', help="Node name for this node")
      (options, args) = p.parse_args(args)
      assert(not args)
      assert(options.node)

      inputs = SmartDict(pickle.loads(zlib.decompress(RAWSTDIN.read())))

      for node in options.node:
         # If -n is given, then we are a direct slave and 
         # should get our config on stdin
         os.environ['FMNODE'] = node
         self.Locations = FmLocations(copyFrom=inputs, slave=node)

         setProcessName("fm _local -n %s %s" % (node, ' '.join(inputs.cmd)))
         cmd = self.Locations.this.subst(inputs.cmd)

         # Call parent initializer with input command (after % substitution done)
         # This will call the appropriate method for the given command
         CommandSetBase.__init__(self, cmd, p)

   def replicate(self, args):
      procs = Procs(retries=self.Locations.this.all2all_retries) 
      errors,ignore = self.Locations.put(args, "/", procs=procs, relativeroot=True, pickn=True, serialize=True, remove=True).collect()
      return errors

   def redistribute(self, args):
      procs = Procs(retries=self.Locations.this.all2all_retries) 
      errors,ignore = self.Locations.put(args, "/", procs=procs, pickn=1, relativeroot=True, serialize=True, hashbasename=True).collect()
      return errors

   def _lscharmod(self, perms, offset, chr):
      perms = list(perms)
      if perms[offset] == "-":
           perms[offset] = chr.upper()
      else:
           perms[offset] = chr.lower()
      return ''.join(perms)

   def df(self, args):
      f = os.popen("df -P " + self.Locations.this.rootdir)
      f.readline() # Throw away header
      disk, size, used, available, percent, mount = f.readline().split()
      disks = {}
      disks[disk] = (int(size)*1024, int(available)*1024)
      RAWSTDOUT.write(pickle.dumps(disks, protocol=2))

   def lsone(self, fname, fs):
      # Construct the dict that is pickled and passed to the client
      d = {}
      d['name'] = fname
      #d['node'] = self.Locations.thisname
      #d['nodename'] = self.Locations.this.name

      if not fs:
          d['user'] = '?'
          d['group'] = '?'
          d['size'] = -1
          d['mtime'] = 0
          d['perms'] = '----------'

          # No stat structure
          return d
      
      # Convert to ls-style human-readable permission mask
      perms = "?"
      for kind in "BLK", "CHR", "DIR", "LNK", "SOCK", "FIFO", "REG":
         if getattr(stat, "S_IS"+kind)(fs.st_mode):
            perms = kind[0].lower().replace("f","p")
      if perms == "r":
         perms = "-"
         
      for who in "USR", "GRP", "OTH":
         for what in "R", "W", "X":
            if fs.st_mode & getattr(stat,"S_I"+what+who):
               c = what.lower()
            else:
               c = "-"
            perms += c

      if stat.S_ISUID & fs.st_mode:
         perms = self._lscharmod(perms, 3, "s")
      if stat.S_ISGID & fs.st_mode:
         perms = self._lscharmod(perms, 6, "s")
      if stat.S_ISVTX & fs.st_mode:
         perms = self._lscharmod(perms, 9, "t")
 
      d['perms'] = perms
      d['size'] = fs.st_size
      d['mtime'] = fs.st_mtime

      try:
         d['user'] = pwd.getpwuid(fs.st_uid).pw_name
      except:
         d['user'] = str(fs.st_uid)

      try:
         d['group'] = grp.getgrgid(fs.st_gid).gr_name
      except:
         d['group'] = fs.st_gid

      return d

   def localstats(self, args, raw=False):
      os.chdir(self.Locations.this.rootdir)  
      args = multiglob(["./" + a for a in args])
      statlist = []
      for apath in args:
         try:
            stats = pickle.load(open(apath, 'rb'))
            stats['statusfile'] = apath
            if stats['nodename'] == self.Locations.thisname:
                # In case of shared directories, we may open status files for other nodes
                statlist.append(stats)
         except:
            print("Error parsing statusfile", apath, file=sys.stderr)

      if raw:
         return statlist
      else:
         RAWSTDOUT.write(pickle.dumps(statlist, protocol=2))
         return 

   def localload(self, args):
      load = {}
      load['loadavg'] = open("/proc/loadavg").readline().strip().split()
      load['cpus'] = os.sysconf('SC_NPROCESSORS_ONLN')
      
      #diskstats = file("/proc/diskstats")
      #for disk in diskstats:
         #disk = disk.strip()
         ## See if this is our ROOTDIR

      RAWSTDOUT.buffer.write(pickle.dumps(load))
      return

   def localjobs(self, args):
      jobs = {}
      jobdir = self.Locations.this.jobdir
      for j in os.listdir(self.Locations.this.jobdir):
         if not j.startswith("."):
            jobs[j] = FmJob(jobdir + "/" + j)
            jobuid = os.stat(jobdir + "/" + j).st_uid
            jobs[j].uid = pwd.getpwuid(jobuid).pw_name
         
      RAWSTDOUT.buffer.write(pickle.dumps(jobs, protocol=2))
      return

   def localrm(self, args):
      p = MethodOptionParser(fixed=["files..."])
      p.add_option('-R', '--recurse', action='store_true', help="recurse")
      p.add_option('--absolute', action='store_true', help="absolute")
      (options, args) = p.parse_args(args)

      if not options.absolute:
         os.chdir(self.Locations.this.rootdir)  
         args = ["./" + a for a in args]

      args = multiglob(args)

      for a in args:
         try:
            os.unlink(a)
         except OSError:
            # Could be a directory
            if options.recurse:
               try:
                  shutil.rmtree(a)
               except:
                  pass #-f semantics are to ignore errors
  
      if Verbose > 0: print(len(args), file=sys.stderr)
      return 
      
   def localls(self, inargs):
      args = []

      if self.Locations.this.cowdir:
         os.chdir(self.Locations.this.cowdir)  
         args += multiglob(["./" + a for a in inargs])

      os.chdir(self.Locations.this.rootdir)  
      args += multiglob(["./" + a for a in inargs])

      if not args:
         return

      procs = Procs()

      output = []
      for apath in args:

         # aname is the virtual name of the file; will be shown to user.
         # So strip the leading ./ that we added to make it relative
         aname = apath[2:].rstrip('/')

         s = os.lstat(apath)
         if stat.S_ISDIR(s.st_mode):
            for f in os.listdir(apath):
               fpath = apath + "/" + f
               fname = aname + "/" + f
               s = None
               try:
                  s = os.lstat(fpath)
               except:
                  pass
               output.append(self.lsone(fname, s))
                
         else:
            output.append(self.lsone(aname, s))

      RAWSTDOUT.write(pickle.dumps(output, protocol=2))
      return

   def kill(self, args=[]):
      """Kill an active scheduler for this node."""
      SchedLock(self.Locations.this.rootdir).kill()
     
   def sched(self, args=[]):
      """Start a scheduler for this node."""

      sl = SchedLock(self.Locations.this.rootdir)
      s = JobScheduler(self.Locations)

      f = open(os.devnull)
      os.dup2(f.fileno(), 0)

      # daemonify
      if not os.fork():
         # Middle-child
         os.setsid()
         if not os.fork():
            # Child

            f = open(self.Locations.this.rootdir + "/.schedlog-" + str(os.getuid()), 'w')
            os.dup2(f.fileno(), 1)
            os.dup2(f.fileno(), 2)

            # For now, the scheduler and FmJob still assume a global Locations var
            global Locations
            Locations = self.Locations
      
            global My_file_prefix
            My_file_prefix = "_".join([self.Locations.thisname, str(os.getpid())]) # New pid and better name!

            if not sl.lock():
               # Somebody else running
               sys.exit(0) 
      
            try:
               s.RunUntilDone()
            except:
               # Try very hard not leave a stale lockfile
               sl.unlock()
               raise
            if Verbose > 1:
               print("Ran until done", file=sys.stderr)
            sl.unlock()

         else:
            self.Locations.cleanup = None #Don't cleanup in parent; child will

         sys.exit(0) # Children should just exit now

      self.Locations.cleanup = None #Don't cleanup in parent; child will


   def wait(self, args):
      """Wait for a specified jobid to complete (and make sure scheduler is running)"""
      self.sched()
      jobid = args[0]
      nextcmd = args[1:]

      jobfile = self.Locations.this.rootdir+"/jobs/"+jobid
      #print >>sys.stderr, "Waiting on", jobfile

      sl = SchedLock(self.Locations.this.rootdir)

      delay = 0.1
      # When the jobfile is gone (or if the scheduler dies prematurely), we're done
      while os.path.isfile(jobfile):
         # Make sure scheduler is running
         if not sl.checkpid():
            # Could have just finished, so make sure jobfile didn't just get deleted
            if os.path.isfile(jobfile):
               # Delay and check again in case the scheduler was just starting
               time.sleep(2)
               if not sl.checkpid() and os.path.isfile(jobfile):
                  print("Error: scheduler exited while job still running.  Dumping log:", file=sys.stderr)
                  sys.stderr.writelines(open(self.Locations.this.rootdir + "/.schedlog-" + str(os.getuid())))
                  return 1

         # Wait 
         # XXX: use famd
         time.sleep(delay)
         delay *= 2
         if delay > 1:
            delay = 1

      # Successful completion
   
      # Do anything else 
      if nextcmd:
         if nextcmd[0] == "redistribute":
            return self.redistribute(nextcmd[1:])
         else:
            print("Unknown command following wait: ", nextcmd, file=sys.stderr)

if __name__ == "__main__":
   FmCommands(sys.argv[1:])
