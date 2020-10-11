#!/bin/bash
find /home/kermit/papa/sat-tools/ -name "*.o"  -print0 | xargs -r -0 /bin/rm
find /home/kermit/papa/sat-tools/ -name "*.hi" -print0 | xargs -r -0 /bin/rm
find /home/kermit/papa/sat-tools/ -name "*~"   -print0 | xargs -r -0 /bin/rm
/bin/rm /home/kermit/papa/sat-tools/test/Main
