() -> ()

d:
	entry
	goto c

b:
	from c
	goto a

a:
	from b
	exit

c:
	from d
	goto b
