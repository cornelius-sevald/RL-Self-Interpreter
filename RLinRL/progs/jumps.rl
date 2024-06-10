() -> ()

d:
from c
exit

b:
from a
goto c

a:
entry
goto b

c:
from b
goto d
