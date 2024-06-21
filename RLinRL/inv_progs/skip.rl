() -> ()

start:
	from mid
	skip
	exit

mid:
	from end
	skip
	skip
	goto start

end:
	entry
	skip
	skip
	skip
	goto mid
