from sage.misc.flatten import flatten
from sage.ext.fast_callable import fast_callable
from sage.rings.semirings.non_negative_integer_semiring import NN
from sage.rings.real_mpfr import RealField
from sage.misc.functional import numerical_approx as N
from sage.functions.log import exp
from sage.functions.log import log
from sage.functions.other import sqrt

'''
Along the process we create the following lists, 
For expresions:
	list1 -> stores the expresions (not variables) needed for the taylor AD
	list2 -> stores the way to build expresions on list1. Needed to determine AD function
	list3 -> stores the list2 with the proper AD function name and the corresponding link or variable 
		 on list1
	parsedList -> stores the lines of C code for AD
	constList1 -> stores the expresions that involves only parameters
	constList2 -> stores the way to build expresions in constList1
	constList3 -> stores the constList2 with the proper construction of the arguments
	parsedConstList -> stores the C code for generating constants


We will use the unified notation:
	vars -> list with the variables of the right side function of the ODE
	pars -> list with the parameters (if any) of the right side function of the ODE
	varpar -> list with vars and pars 
'''

def createLists (f, pars):
	'''
	Creates list1 and list 2 from the right side function f of an ODE:
	input: 
		f -> right side function for ODE system
		pars -> list with the parameters on f
	output:
		list1 and list2


	Example with Lorenz Equation
	sage: var('t, x, y, z')		# variables for lorenz equations
	sage: var('s, r, b')		# parameters for lorenz equations
	sage: f(t,x,y,z) = [s*(y-x), x*(r-z) - y, x*y - b*z]	# Right side function for Lorenz equation

	'''
	vars = f[0].arguments ()				# gets the list of variables from function f
	varpar = list (vars) + list (pars)			# gets the list of vars and pars totegher
	_f = f (*vars).function (varpar)	# _f is f but with vars and pars as arguments


	fastCallList = flatten ([fast_callable (i,vars=varpar).op_list () for i in f], max_level=1)
		# This list is the fast callable version of f using a stack-mode call
	'''
	We create create the lists list1, list2 and stack.
	stack will be expresion stack-list

	'''
	list1 = []; list2 = []; stack = [];
	'''
	Starts parser on fastCallList. 
	'''
	for s in fastCallList:
		if s[0] == 'load_arg':			# Loads a variable in stack. no changes on list1, or list2
			stack.append (varpar[s[1]])	# appends the variable or parameter on symbolic stack

		elif s[0] == 'ipow':			# Integer power. 
			if s[1] in NN:			# If natural, parser as products
				basis = stack[-1]
				for j in range (s[1]-1):
					a=stack.pop (-1)
					stack.append (a*basis)
					list1.append (stack[-1])
					list2.append (('mul', a, basis))
			elif -s[1] in NN:
				basis = stack[-1]
				for j in range (-s[1]-1):
					a=stack.pop (-1)
					stack.append (a*basis)
					list1.append (stack[-1])
					list2.append (('mul', a, basis))
				a = stack.pop (-1);
				stack.append (1/a);
				list1.append (stack[-1])
				list2.append (('div', 1, a))
			else:				# Attach as normal power
				a = stack.pop (-1)	#basis
				stack.append (a ** s[1])
				list1.append (stack[-1])
				list2.append (('pow', a, s[1]))

		elif s[0] == 'load_const':		# Loads a constant value on stack. Not in list1 or list2
			stack.append (s[1])

		elif s == 'neg':			# multiplies by -1.0
			a = stack.pop (-1)		# expresion to be multiplied by -1
			stack.append (-a)
			list1.append (stack[-1])
			list2.append (('mul', -1, a))

		elif s == 'mul':			# Product
			a=stack.pop (-1)
			b=stack.pop (-1)
			list2.append (('mul', a, b))
			stack.append (a*b)
			list1.append (stack[-1])

		elif s == 'div':			# divission Numerator First.
			b=stack.pop (-1)		# denominator (after a in stack)
			a=stack.pop (-1)		# numerator (before b in stack)
			if expresionIsConstant (b, pars):
				list1.append(1/b)
				list2.append(('div', 1, b))
				b = 1/b;
				stack.append (a*b)
				list1.append(stack[-1])
				list2.append (('mul', a, b))
			else:
				list2.append (('div', a, b))
				stack.append (a/b)
				list1.append (stack[-1])

		elif s == 'add':			# addition
			b = stack.pop (-1)		# second operand
			a = stack.pop (-1)		# first operand
			stack.append (a+b)
			list1.append (stack[-1])
			list2.append (('add', a, b))

		elif s == 'pow':			# any other pow
			b = stack.pop (-1)		# exponent
			a = stack.pop (-1)		# basis
			stack.append (a**b)
			list1.append (stack[-1])
			list2.append (('pow', a, b))

		elif s[0] == 'py_call' and 'sqrt' in str (s[1]):	# square root. Compute as power
			a = stack.pop (-1)		# argument of sqrt
			stack.append (sqrt (a))
			list1.append (stack[-1])
			list2.append (('pow', a, 0.5))

		elif s[0] == 'py_call' and str (s[1]) == 'log':	# logarithm
			a = stack.pop (-1);		# argument of log
			stack.append (log (a))
			list1.append (stack[-1])
			list2.append (('log', a))

		elif s[0] == 'py_call' and str (s[1]) == 'exp':
			a = stack.pop (-1);		# argument of exp
			stack.append (exp (a))
			list1.append (stack[-1])
			list2.append (('exp', a))

		elif s[0] == 'py_call' and str (s[1]) == 'sin':		# sine. For AD needs computation of cos
			a = stack.pop (-1)
			stack.append (sin (a))
			list1.append (sin (a))
			list1.append (cos (a))
			list2.append (('sin', a))
			list2.append (('cos', a))

		elif s[0] == 'py_call' and str (s[1]) == 'cos':		# cosine. For AD needs computation of sin
			a = stack.pop (-1)
			stack.append (cos (a))
			list1.append (sin (a))
			list1.append (cos (a))
			list2.append (('sin', a))
			list2.append (('cos', a))
		elif s[0] == 'py_call' and str (s[1]) == 'tan':
			a = stack.pop (-1)
			stack.append (tan (a))
			list1.append (sin (a))
			list1.append (cos (a))
			list1.append (tan (a))
			list2.append (('sin', a))
			list2.append (('cos', a))
			list2.append (('div', sin (a), cos (a)))

	return list1, list2



def removeRepeated (list1, list2):
	'''
	Removes repeated expresions from list1 and list2
	'''
	for s1 in range (len (list1) - 1):
		s2=s1+1
		while s2 < len (list1):
			if list1[s2] == list1[s1]:
				list1.pop(s2)
				list2.pop(s2)
			else:
				s2 += 1

def expresionIsConstant (expresion, pars):
	'''
	Returns whether an expresion is constant or not, that is, its variables are included in set pars

	'''
	return  (set (expresion.variables ()).issubset (set (pars)))


def removeConstants (list1, list2, pars):
	'''
	Remove constant expresions from list1 and list2.
	If the constant expresion does not contain any parameter, it is just removed
	otherwise it is moved into constList1 and constList2
	'''
	i=0
	RR = RealField ()			# define Real field
	constList1=[]
	constList2=[]
	while i < len(list1):
		if (list1[i] in RR):		# checks if it is a Real Number of SAGE (no parameters at all)
			list1.pop(i)
			list2.pop(i)
		elif expresionIsConstant (list1[i], pars):	# checks if there are only parameters
			constList1.append (list1.pop(i))
			constList2.append (list2.pop(i))
		else:
			i+=1
	return constList1, constList2


def createCodeList (list1, list2, constList1, f, pars):
	'''
	Creates list3. In list3 we identify each expresion with the correspondent variable, parameter,
	link, constant expresion or real constant

	'''
	list3=[]
	vars = f[0].arguments()		# variables of the function
	for s in list2:			# s is a tuple with the information to build expresions of list1
		oper = s[0]		# the external operator of the expresion
		if oper in ['log', 'exp', 'sin', 'cos', 'tan']:	# unary operator
						# argument cannot be parameter, real number or constant expresion.
						# those cases are stored in constList1 and constList2
			a = s[1]		# identify operand
			if a in vars:		# case of variable
				if a == vars[0]:
					list3.append ((oper, 'T'))
				else:
					list3.append ((oper, 'series[{}]'.format (vars.index (a) - 1)))
			else:
				list3.append ((oper, 'l[{}]'.format (list1.index (a))))
		else:			# binary operator
			a = s[1]	# firt operand
			b = s[2]	# second operand
			constA = False	# flags to determine whether any of them are constant
			constB = False
					# not possible both of them

			if a in vars:	# if a is a variable
				if a == vars[0]:
					aa = 'T'
				else:
					aa = 'series[{}]'.format (vars.index (a) - 1)	# corresponding string
			elif a in list1:	# if a is a link
				aa = 'l[{}]'.format (list1.index (a))		# corresponding string
			else:		# ok, a is constant
				constA = True			# constant flag on
				if a in constList1:		# a constant expresion
					aa = 'c[{}]'.format (constList1.index (a))
				elif a in pars:			# a parameter
					aa = 'par[{}]'.format (pars.index (a))
				else:				# a is a real constant. 
					aa = str (N (a))	# write as a string

			if b in vars:	# same with b
				if b == vars[0]:
					bb = 'T'
				else:
					bb = 'series[{}]'.format (vars.index (b) - 1)
			elif b in list1:
				bb = 'l[{}]'.format (list1.index (b))
			else:
				constB = True
				if b in constList1:
					bb = 'c[{}]'.format (constList1.index (b))
				elif b in pars:
					bb = 'par[{}]'.format (pars.index (b))
				else:
					bb = str (N (b))

			# we set the const argument in the first place
			if constA:
				oper += '_c'
				bb, aa = aa,bb
			elif constB:
				oper += '_c'
			list3.append ((oper, aa, bb))

	return list3



def createConstCodeList (constList1, constList2, pars):
	'''
	Creates constList3. In constList3 we identify each expresion with the correspondent parameter,
	constant expresion or real constant

	'''
	constList3 = []
	for s in constList2:
		oper = s[0]

		if oper in ['log', 'exp', 'sin', 'cos', 'tan']:	# unary operator
			a = s[1]		# get operand (constant expresion or parameter)
			if a in pars:		# checks if is a parameter
				constList3.append ((oper, 'par[{}]'.format (pars.index (a))))
			else:
				constList3.append ((oper, 'c[{}]'.format (constList1.index (a))))
	
	        else:						# binary operator
						# now any of the operands (not both) can be a real number
			a=s[1]
			b=s[2]
			if a in pars:		# check if a is parameter
				aa = 'par[{}]'.format (pars.index (a))
			elif a in constList1:	# check if a is constant expresion
				aa = 'c[{}]'.format (constList1.index (a))
			else:			# a is a real number
				aa = '(' + str (N (a)) + ')'
				# now the do de same with b
			if b in pars:
				bb = 'par[{}]'.format (pars.index (b))
			elif b in constList1:
				bb = 'c[{}]'.format (constList1.index (b))
			else:
				bb = '(' + str (N (b)) + ')'
	            
			constList3.append ((oper, aa, bb))

	return constList3




def createParsedConstList (constList3):
	'''
	Creates the lines of C code to generate constant expresions in the code

	'''
	parsedConstList = []

	for i in range (len (constList3)):
		codeLine = constList3[i]
		string = '\tc[{}] = '.format(i)
		if codeLine[0] == 'add':
			string += codeLine[1] + ' + ' + codeLine[2] + ';'
		if codeLine[0] == 'mul':
			string += codeLine[1] + ' * ' + codeLine[2] + ';'
		if codeLine[0] == 'div':
			string += codeLine[1] + ' / ' + codeLine[2] + ';'
		if codeLine[0] == 'exp':
			string += 'exp (' + codeLine[1] + ');'
		if codeLine[0] == 'log':
			string += 'log (' + codeLine[1] + ');'
		if codeLine[0] == 'sin':
			string += 'sin (' + codeLine[1] + ');'
		if codeLine[0] == 'cos':
			string += 'cos (' + codeLine[1] + ');'
		if codeLine[0] == 'tan':
			string += 'tan (' + codeLine[1] + ');'
		parsedConstList.append (string)

	return parsedConstList


def createParsedList (list1, list3, f):
	'''
	Creates the lines of C code for AD of right side member f of the ODE

	'''
	vars = list(f[0].arguments())
	parsedList = []
	for i in range(len(list3)):
		codeLine = list3[i]
		string = '\t\t'
		if codeLine[0] == 'add':
			string += 'dp_sumAD (i, l[{}], '.format(i) + codeLine[1] + ', ' + codeLine[2] + ');'
		elif codeLine[0] == 'add_c':
			string += 'dp_smCAD (i, l[{}], '.format(i) + codeLine[1] + ', ' + codeLine[2] + ');'
		elif codeLine[0] == 'mul':
			string += 'dp_mulAD (i, l[{}], '.format(i) + codeLine[1] + ', ' + codeLine[2] + ');'
		elif codeLine[0] == 'mul_c':
			string += 'dp_mlCAD (i, l[{}], '.format(i) + codeLine[1] + ', ' + codeLine[2] + ');'
		elif codeLine[0] == 'pow_c':
			string += 'dp_powAD (i, l[{}], '.format(i) + codeLine[1] + ', ' + codeLine[2] + ');'
		elif codeLine[0] == 'div':
			string += 'dp_divAD (i, l[{}], '.format(i) + codeLine[1] + ', ' + codeLine[2] + ');'
		elif codeLine[0] == 'div_c':
			string += 'dp_invAD (i, l[{}], '.format(i) + codeLine[1] + ', ' + codeLine[2] + ');'
		elif codeLine[0] == 'exp':
			string += 'dp_expAD (i, l[{}], '.format(i) + codeLine[1] + ');'
		elif codeLine[0] == 'log':
			string += 'dp_logAD (i, l[{}], '.format(i) + codeLine[1] + ');'
		elif codeLine[0] == 'sin':
			string += 'dp_sinAD (i, l[{}], '.format(i) + codeLine[1] + ', l[{}]);'.format(i+1)
		elif codeLine[0] == 'cos':
			string += 'dp_cosAD (i, l[{}], '.format(i) + codeLine[1] + ', l[{}]);'.format(i-1)

		parsedList.append(string)
	

	parsedList.append('\n')
	list1Extended = vars + list1
	indices = [list1Extended.index (i(*vars)) for i in f]
				# locate indeces of each expresion of f

	for i in range (1, len (vars)):
		aux = indices[i-1]
		if aux == 0:			# derivative corresponds to t
			parsedList.append ('\t\tseries[{}][i+1] = T[i] / (i+1.0);'.format (i-1))
	        elif aux < len(vars):		# derivative corresponds to a variable
			parsedList.append ('\t\tseries[{}][i+1] = series[{}][i] / (i+1.0);'.format(i-1, aux - 1))
		else:			# derivatie corresponds to an expresion
			parsedList.append ('\t\tseries[{}][i+1] = l[{}][i] / (i+1.0);'.format(i-1, aux - len(vars)))	

	return parsedList



def generateCode (f, pars):
	'''
	Creates list1 and list 2 from the right side function f of an ODE:
	input: 
		f -> right side function for ODE system
		pars -> list with the parameters on f
	output:
		C code for Automatic Differentiation


	Example with Lorenz Equation
	sage: var('t, x, y, z')		# variables for lorenz equations
	sage: var('s, r, b')		# parameters for lorenz equations
	sage: f(t,x,y,z) = [s*(y-x), x*(r-z) - y, x*y - b*z]	# Right side function for Lorenz equation
	sage: generateCode (f, [s, r, b])

	'''
	list1, list2 = createLists (f, pars)
	removeRepeated (list1, list2)
	constList1, constList2 = removeConstants (list1, list2, pars)
	list3 = createCodeList(list1, list2, constList1, f, pars)
	constList3 = createConstCodeList (constList1, constList2, pars)

	parsedConstList = createParsedConstList (constList3)
	parsedList = createParsedList (list1, list3, f)
	vars = f[0].arguments ()
	auxSet = set(flatten([i.variables() for i in f]))	# set of variables in f
	if set ([vars[0]]).issubset (auxSet):				# non autonomous system
		print '\tdouble T[order];'
		print '\tfor (i=2; i<order; i++) T[i] = 0.0;'
		print '\tT[0] = t;'
		print '\tT[1] = 1.0;'

	if len(list1) > 0:	# checks if there are links
		print '\tdouble l[{}][order];'.format (len (list1))
	if len(constList1) > 0: # checks if there are constant expresions
		print '\tdouble c[{}];'.format (len (constList1))
	for s in parsedConstList:
        	print s
	print '\tfor (i=0; i<order; i++) {'
	for s in parsedList:
		print s
	print '\t}'



