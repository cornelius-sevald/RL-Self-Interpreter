(a b c) -> (a b c)

in:
entry
goto mid

mid:
from in
  a += b + c
  b += a + c
  c += a + b
goto out

out:
from mid
exit
