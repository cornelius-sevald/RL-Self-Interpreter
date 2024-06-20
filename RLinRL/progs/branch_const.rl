() -> ()

in:
entry
if 'yes goto left1 else right1

left1:
from in
  assert('yes)
goto mid

right1:
from in
  assert(! 'yes)
goto mid

mid:
fi 'yes from left1 else right1
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
