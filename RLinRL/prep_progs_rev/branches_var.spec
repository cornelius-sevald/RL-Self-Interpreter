prog = '((in.(ENTRY.(((UPDATE.(XOR.(yess.(CONST.0)))).((UPDATE.(XOR.(nos.(CONST.0)))).nil)).(IF.((VAR.a).(yes1.no1)))))).((yes1.((FROM.in).(((UPDATE.(ADD.(yess.(CONST.1)))).nil).(GOTO.mid1)))).((no1.((FROM.in).(((UPDATE.(ADD.(nos.(CONST.1)))).nil).(GOTO.mid1)))).((mid1.((FI.((VAR.a).(yes1.no1))).(nil.(IF.((VAR.b).(yes2.no2)))))).((yes2.((FROM.mid1).(((UPDATE.(ADD.(yess.(CONST.1)))).nil).(GOTO.mid2)))).((no2.((FROM.mid1).(((UPDATE.(ADD.(nos.(CONST.1)))).nil).(GOTO.mid2)))).((mid2.((FI.((VAR.b).(yes2.no2))).(nil.(IF.((VAR.c).(yes3.no3)))))).((yes3.((FROM.mid2).(((UPDATE.(ADD.(yess.(CONST.1)))).nil).(GOTO.out)))).((no3.((FROM.mid2).(((UPDATE.(ADD.(nos.(CONST.1)))).nil).(GOTO.out)))).((out.((FI.((VAR.c).(yes3.no3))).(nil.EXIT))).nil))))))))))
output = '((a.nil).((b.nihil).((c.nil).((nos.2).((yess.1).nil)))))
