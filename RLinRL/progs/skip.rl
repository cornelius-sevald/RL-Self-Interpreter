() -> ()

start:
entry
  skip
goto mid

mid:
from start
  skip
  skip
goto end

end:
from mid
  skip
  skip
  skip
exit
