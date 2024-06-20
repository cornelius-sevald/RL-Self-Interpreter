(a b c) -> (a b c)

in:
entry
goto mid

mid:
from in
  a += (b * c) + ((c / (b * '2)) - b)
  b += (a * c) + ((c / (a * '2)) - a)
  c += (a * b) + ((b / (a * '2)) - a)
goto out

out:
from mid
exit
