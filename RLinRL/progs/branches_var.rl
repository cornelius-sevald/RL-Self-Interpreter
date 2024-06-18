(a b c) -> (a b c)

in:
entry
if a goto yes1 else no1

yes1:
from in
goto mid1

no1:
from in
goto mid1

mid1:
fi a from yes1 else no1
if b goto yes2 else no2

yes2:
from mid1
goto mid2

no2:
from mid1
goto mid2

mid2:
fi b from yes2 else no2
if c goto yes3 else no3

yes3:
from mid2
goto out

no3:
from mid2
goto out

out:
fi c from yes3 else no3
exit
