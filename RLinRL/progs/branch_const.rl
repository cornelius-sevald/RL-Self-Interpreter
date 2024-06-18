() -> ()

in:
entry
if 'ruth goto left1 else right1

left1:
from in
  assert('ruth)
goto mid

right1:
from in
  assert(! 'ruth)
goto mid

mid:
fi 'ruth from left1 else right1
if 'nil goto left2 else right2

left2:
from mid
  assert('nil)
goto out

right2:
from mid
  assert(! 'nil)
goto out

out:
fi 'nil from left2 else right2
exit
