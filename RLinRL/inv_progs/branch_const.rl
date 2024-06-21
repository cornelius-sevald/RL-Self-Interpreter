() -> ()

in:
	fi 'yes
		from left1
		else right1
	exit

left1:
	from mid
	assert('yes)
	goto in

right1:
	from mid
	assert(!('yes))
	goto in

mid:
	fi 'nil
		from left2
		else right2
	if 'yes
		goto left1
		else right1

left2:
	from out
	assert('nil)
	goto mid

right2:
	from out
	assert(!('nil))
	goto mid

out:
	entry
	if 'nil
		goto left2
		else right2
