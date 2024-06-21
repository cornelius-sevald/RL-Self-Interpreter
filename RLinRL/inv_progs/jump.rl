() -> ()

init:
	from stop
	exit

stop:
	entry
	goto init
