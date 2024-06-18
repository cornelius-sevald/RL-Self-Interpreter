() -> ()

init:
entry
goto loop

loop:
fi 'nil from loop else init
if 'nil goto loop else stop

stop:
from loop
exit
