(x i) -> (x i)

in:
entry
  assert(i < '10)
goto loop

loop:
fi i < '10 from in else loop
  i += '1
  x += i
if i < '10 goto out else loop

out:
from loop
exit
