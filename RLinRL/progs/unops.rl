(a b c) -> (a b c yess nos) with (nums)

in:
entry
  nums ^= '(1 . (2 . 4))
  yess ^= '0
  nos ^= '0
if ! a goto yes1 else no1

yes1:
from in
  yess += hd nums
goto mid1

no1:
from in
  nos += hd nums
goto mid1

mid1:
fi ! a from yes1 else no1
if ! (! b) goto yes2 else no2

yes2:
from mid1
  yess += hd (tl nums)
goto mid2

no2:
from mid1
  nos += hd (tl nums)
goto mid2

mid2:
fi ! (! b) from yes2 else no2
if ! (! (! c)) goto yes3 else no3

yes3:
from mid2
  yess += tl (tl nums)
goto out

no3:
from mid2
  nos += tl (tl nums)
goto out

out:
fi ! (! (! c)) from yes3 else no3
  nums ^= '(1 . (2 . 4))
exit
