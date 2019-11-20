from functools import wraps

stack = [None for x in range(100)]
rsp = bp = 0 #rsp is the stack pointer, bp the base pointer
rip = 0 #instruction pointer

exit_code = 0

start = 0
start_count = 0

stack_overflow = ValueError("***Stack Overflow***")

variables = {}
labels = {}
last_global_label = None

debug = False


def stack_init(size=100):
    global stack
    global rsp
    global bp

    rsp = bp = 0

    stack = [None for x in range(size)]

def stack_clear():
    global stack
    for i in range(len(stack)): stack[i] = None


def var_clear():
    global variables
    variables = {}

def sp_reset():
    global rsp
    global bp
    rsp = bp = 0

def sp_set(val):
    global rsp
    rsp = val

def sp_add(val):
    val = val[1]
    sp_set(rsp + val)

def sp_sub(val):
    val = val[1]
    sp_set(rsp - val)

def stack_reset():
    sp_reset()
    stack_clear()


def rip_set(val):
    global rip
    rip = val

def rip_reset():
    rip_set(0)


def label_reset():
    global labels
    global last_global_label
    labels = {}
    last_global_label = None


def make_label(ins, address):
    global labels
    global last_global_label

    label_name = ins[1]
    
    if label_name[0] == '.':
        if last_global_label is None:
            raise ValueError
        label_name = last_global_label + label_name
    else:
        last_global_label = label_name

    if labels.get(label_name) is not None:
            raise ValueError
    labels[label_name] = address

    return ['SKIP', 'LAB']

def make_func_label(func):
    global labels
    global last_global_label

    if labels.get(func.name) is not None:
            raise ValueError

    labels[func.name] = func.address

    last_global_label = func.name

    return ['SKIP', 'FUNC']


def spop():
    global rsp
    val = stack[rsp]
    rsp -= 1
    return val

def spush(val):
    global rsp
    global stack
    rsp += 1
    stack[rsp] = val


def fpush(ins):
    global rsp
    global stack
    stack[rsp + 1] = stack[rsp]
    rsp += 1


def ipush(ins):
    global rsp
    global stack
    i = stack[rsp]
    stack[rsp] = stack[i]


def rpush(ins):
    global rsp
    global stack
    i = (rsp - 1) + stack[rsp]
    stack[rsp] = stack[i]


def rbpush(ins):
    global rsp
    global stack
    i = bp + stack[rsp]
    stack[rsp] = stack[i]



def sswap(ins):
    global rsp
    global stack
    tmp = stack[rsp]
    stack[rsp] = stack[rsp - 1]
    stack[rsp - 1] = tmp


def iswap(ins):
    global stack
    global rsp
    i = stack[rsp]
    rsp -= 1
    tmp = stack[rsp]
    stack[rsp] = stack[i]
    stack[i] = tmp


def rswap(ins):
    global stack
    global rsp
    i = (rsp - 1) + stack[rsp]
    rsp -= 1
    tmp = stack[rsp]
    stack[rsp] = stack[i]
    stack[i] = tmp


def rbswap(ins):
    global stack
    global rsp
    i = bp + stack[rsp]
    rsp -= 1
    tmp = stack[rsp]
    stack[rsp] = stack[i]
    stack[i] = tmp



def smath(op):
    def func(ins):
        global stack
        global rsp
        a = stack[rsp]
        b = stack[rsp - 1]
        rsp -= 1
        stack[rsp] = op(a, b)
    
    return func

sadd = smath(lambda a, b: a + b)
ssub = smath(lambda a, b: a - b)
smult = smath(lambda a, b: a * b)
sexp = smath(lambda a, b: a ** b)
sdiv = smath(lambda a, b: a / b)
sdivint = smath(lambda a, b: a // b)
smod = smath(lambda a, b: a % b)
slshift = smath(lambda a, b: a << b)
srshift = smath(lambda a, b: a >> b)
sxor = smath(lambda a, b: a ^ b)
sor = smath(lambda a, b: a | b)
sand = smath(lambda a, b: a & b)
sgt = smath(lambda a, b: a > b)
sgte = smath(lambda a, b: a >= b)
slt = smath(lambda a, b: a < b)
slte = smath(lambda a, b: a <= b)
seq = smath(lambda a, b: a == b)
sis = smath(lambda a, b: a is b)
sne = smath(lambda a, b: a != b)

def sjump(ins):
    global rip
    address = spop()
    rip = address - 1

def jump_template(comp):
    def func(ins):
        global rip
        address = spop()
        if stack[rsp] == comp:
            rip = address - 1

    return func


sjumpt = jump_template(True)
sjumpf = jump_template(False)
  

def scomplement(ins):
    global stack
    val = stack[rsp]
    stack[rsp] = ~val

def sassign(ins):
    global variables
    global rsp
    name = stack[rsp]
    variables[name] = stack[rsp - 1]
    rsp -= 1

def sload(ins):
    global variables
    global stack
    stack[rsp] = variables[stack[rsp]]

def oload(ins):
    global stack
    global rsp
    o = stack[rsp]
    field = stack[rsp - 1]
    rsp -= 1
    stack[rsp] = o[field]

def oassign(ins):
    global stack
    global rsp
    o = stack[rsp]
    field = stack[rsp - 1]
    rsp -= 2
    o[field] = stack[rsp]





def smake_iter(type_iter):
    def func(ins):
        global stack
        global rsp
        num_items = spop()
        spush(type_iter([spop() for x in range(num_items)]))
    
    return func


smake_tuple = smake_iter(tuple)
smake_list = smake_iter(list)

def smake_object(ins):
    global stack
    global rsp
    num_pairs = stack[rsp]
    items = stack[(rsp - num_pairs * 2):rsp]
    key = True
    lkey = None
    o = {}
    for i in items:
        if key:
            if not isinstance(i, Symbol):
                raise ValueError
            lkey = i
            key = False
        else:
            if isinstance(i, Symbol):
                raise ValueError
            o[lkey] = i
            key = True
        rsp -= 1
    stack[rsp] = o
    

class VFunc:
    def __init__(self, name, nargs, address):
        self.name = name
        self.nargs = nargs
        self.address = address


class VMethod(VFunc):
    def __init__(self, name, nargs, address, obj):
        super().__init__(name, nargs, address)
        self.bound = obj


def scall(ins):
    global rip
    global rsp
    global stack

    func = stack[rsp]
    if not isinstance(func, VFunc):
        raise ValueError("Cannot call nonfunction object")
    if len(stack[rsp - 1]) != func.nargs:
        raise ValueError("Incorrect number of arguments for function call")
    stack[rsp] = rip
    rip = func.address - 1

def acall(ins):
    global rip
    global rsp
    global stack

    address = stack[rsp]
    stack[rsp] = rip
    rip = address - 1


def obind(ins):
    global rip
    global rsp
    global stack

    func = stack[rsp]
    if not isinstance(func, VFunc):
        raise ValueError("Cannot bind object to nonfunction object")

    obj = stack[rsp - 1]
    method = VMethod(func.name, func.nargs, func.address, obj)
    rsp -= 1
    stack[rsp] = method    


def sret(ins):
    global stack
    global rsp
    global rip
    
    rip = stack[rsp]
    rsp -= 1


def strip_str(s):
    token = s[0]
    if token != s[-1] or (token != "'" and token != '"'):
        return None

    s = s[1:-1]

    buff = [None for x in range(len(s))]
    ignore = False
    i = 0

    for c in s:
        if ignore:
            if c == 'n':
                c = '\n'
            elif c == '\t':
                c = '\t'
            buff[i] = c
            i += 1
            ignore = False
            continue

        if c == '\\':
            ignore = True
            continue

        if c == "'" or c == '"':
            if c == token:
                return None
            continue

        buff[i] = c
        i += 1

    return "".join(buff[:i])

class Symbol(str):
    pass


def scompile(code, ins):
    global variables
    global labels
    global start
    global start_count

    name = ins[0]
    if name == 'STR':
        ins[1] = strip_str(ins[1])
    elif name == 'INT':
        ins[1] = int(ins[1])
    elif name == 'FLT':
        ins[1] = float(ins[1])
    elif name == 'SYM':
        ins[1] = Symbol(ins[1])
    elif name == 'BOOL':
        ins[1] = bool(ins[1])
    elif name == 'LABL':
        ins = make_label(ins, len(code) + 1)
        print(f"*** LABL {ins} ***")
    elif name == 'FUNC':
        ins[1] = Symbol(ins[1])
        ins[2] = int(ins[2])
        address = len(code) + 1
        fn = VFunc(ins[1], ins[2], address)
        variables[fn.name] = fn
        ins = make_func_label(fn)
    elif name == "#":
        ins = ['SKIP', 'COM']
    elif name[0] == '$':
        print(f"*** ADDRESS {name} ***")
        name = name[1:]
        if name[0] == '.':
            if last_global_label is None:
                raise ValueError
            name = last_global_label + name
        ins = ['ADDRESS', name]
    elif name == 'NONE':
        ins = ['NONE', None]

    elif name == 'START':
        if start_count > 0:
            raise ValueError
        start_count += 1
        start = len(code)
        ins = ['SKIP', 'BEGINPROGRAM']


 
    return ins

      

def parser(code):
    parsed = []
    found_ins = False
    n = 0

    for i, c in enumerate(code):
        if c == ';':
            if not found_ins:
                return None
            found_ins = False
            line = code[n:i].split()
            line = scompile(parsed, line)
            parsed.append(line)
            continue

        if not c.isspace() and not found_ins:
            n = i
            found_ins = True

    # case of last line being imcomplete:
    if found_ins:
        return None

    return parsed


def interpreter_template(ops):
    def func(code):
        global stack
        global rip
        global start
        global debug

        rip = start
        
        if debug:
            print(f"*** STARTING ON LINE: {start} ***")

        while rip < len(code):
            ins = code[rip]
            name = ins[0]
            op = ops.get(name)
            if debug:
                print(f"*** EXEC INS '{name}': {ins} ***", end='')
            if op is None:
                print('')
                raise ValueError(f"Unknown instruction {name}")
            op(ins)
            if debug:
                print(f" RESULT: {stack[rsp]}")
            rip += 1

        print(f"\n*** END OF PROGRAM; TERMINATED WITH EXIT CODE: {exit_code} ***")
    
    return func


def push_literal(ins):
    global rsp
    global stack
    rsp += 1
    stack[rsp] = ins[1]

def stack_pointer_add(ins):
    global rsp
    global stack
    rsp = (rsp - 1) + stack[rsp]


def stack_pointer_sub(ins):
    global rsp
    global stack
    rsp = (rsp - 1) - stack[rsp]

def stack_pointer_inc(ins):
    global rsp
    rsp += 1


def stack_pointer_dec(ins):
    global rsp
    rsp -= 1

def stack_pointer_set(ins):
    global rsp
    global stack
    rsp = stack[rsp]

def stack_pointer_get(ins):
    global rsp
    global stack
    old_rsp = rsp
    rsp += 1
    stack[rsp] = old_rsp


def stack_pointer_rget(ins):
    global rsp
    global stack
    stack[rsp] = (rsp - 1) + stack[rsp]

def scollapse(ins):
    global rsp
    global stack
    stack[rsp - 1] = stack[rsp]
    rsp -= 1


def icollapse(ins):
    global rsp
    global stack
    i = stack[rsp]
    stack[i] = stack[rsp - 1]
    rsp = i


def rcollapse(ins):
    global rsp
    global stack
    i = (rsp - 1) + stack[rsp]
    stack[i] = stack[rsp - 1]
    rsp = i


def rbcollapse(ins):
    global rsp
    global stack
    i = bp + stack[rsp]
    stack[i] = stack[rsp - 1]
    rsp = i



def sindex(ins):
    o = spop()
    i = spop()
    spush(o[i])

def ssetindex(ins):
    o = spop()
    i = spop()
    o[i] = stack[rsp]

''' 
    R = relative of rsp, I = absolute index of stack, no prefix works on top of stack
'''

def base_pointer_set(ins):
    global rsp
    global stack
    global bp
    bp = stack[rsp]
    rsp -= 1

def base_pointer_get(ins):
    global rsp
    global stack
    rsp += 1
    stack[rsp] = bp

def base_pointer_rget(ins):
    global stack
    global rsp
    stack[rsp] = bp + stack[rsp]

def base_pointer_save(ins):
    global stack
    global rsp
    global bp
    rsp += 1
    stack[rsp] = bp
    bp = rsp

def base_pointer_restore(ins):
    global stack
    global rsp
    global bp
    rsp = bp
    bp = stack[rsp]
    rsp -= 1

def larg(ins):
    global stack
    global rsp
    args = stack[bp - 2]
    arg = args[stack[rsp]]
    stack[rsp] = arg

def largs(ins):
    global stack
    global rsp
    args = stack[bp - 2]
    rsp += 1
    stack[rsp] = args

def sleave(ins):
    global stack
    global rsp
    global rip
    result = stack[rsp]
    base_pointer_restore(ins)
    rip = stack[rsp]
    stack[rsp] = result

def sexit(ins):
    global rip
    global exit_code
    exit_code = stack[rsp]
    rip = len(stack) + 1

def sendprog(ins):
    global rip
    rip = len(stack) + 1

def sprint(ins):
    print(stack[rsp])

def sprintn(ins):
    global rsp
    global stack
    n = stack[rsp]
    rsp -= 1

    for i in range(n):
        print(stack[rsp - i], end='')

def resolve_address(ins):
    global rsp
    global stack
    global labels
    rsp += 1
    stack[rsp] = labels[ins[1]]

def print_stack(ins):
    print("*** STACK INFORMATION: ***")
    print(f"LENGTH: {len(stack)}\n")
    print(stack)
    print('\n')


instruction_operations = {
    'ADDRESS': resolve_address,
    'INT': push_literal, 'STR': push_literal, 'FLT': push_literal, 'SYM': push_literal,
    'BOOL': push_literal, 'NONE': push_literal,

    'LIST': smake_list, 'TUPL': smake_tuple, 'OBJECT': smake_object,

    'SWAP': sswap, 'ISWAP': iswap, 'RSWAP': rswap, 'RBSWAP': rbswap,
    'POP': scollapse, 'IPOP': icollapse, 'RPOP': rcollapse, 'RBPOP': rbcollapse,
    'PUSH': fpush, 'IPUSH': ipush, 'RPUSH': rpush, 'RBPUSH': rbpush,
    
    'SKIP': lambda a: a,

    'JMP': sjump, 'JMPT': sjumpt, 'JMPF': sjumpf,
    
    'SPINC': stack_pointer_inc, 'SPDEC': stack_pointer_dec, 'SPADD': stack_pointer_add,
    'SPSUB': stack_pointer_sub, 'SPSET': stack_pointer_set, 'SP': stack_pointer_get,
    'RSP': stack_pointer_rget,

    'BP': base_pointer_get, 'RBP': base_pointer_rget, 'BPSET': base_pointer_set,
    'SAVE': base_pointer_save, 'RESTORE': base_pointer_restore,

    'INDEX': sindex, 'SETINDEX': ssetindex,

    'PRINT': sprint, 'PRINTN': sprintn, 'PRINTSTACK': print_stack,

    'CALL': scall, 'ACALL': acall, 'LARGS': largs, 'LARG': larg, 
    'RET': sret, 'LEAVE': sleave, 'BIND': obind,

    'OLOAD': oload, 'OSET': oassign, 'LOAD': sload, 'SET': sassign,

    'ADD': sadd, 'SUB': ssub,'MULT': smult, 'MOD': smod, 
    'DIV': sdiv, 'DIVINT': sdivint, 'EXP': sexp,
    'LSHFT': slshift, 'RSHFT': srshift, 
    'XOR': sxor, 'OR': sor, 'AND': sand, 'COMPLEMENT': scomplement, 
    'GT': sgt, 'GTE': sgte, 'LT': slt, 'LTE': slte,
    'EQ': seq, 'IS': sis, 'NEQ': sne,

    'EXIT': sexit, 'ENDPROGRAM': sendprog
}


interpreter = interpreter_template(instruction_operations)


def reset_all():
    global start
    global start_count
    global exit_code
    global debug
    start = start_count = exit_code = 0
    stack_clear()
    var_clear()
    label_reset()
    rip_reset()
    debug = False


def main(code, file=False):
    if file:
        with open(code, "r") as source:
            txt = source.read()
            code = "".join(txt)
    parsed = parser(code)
    print(parsed, '\n')
    print("Parsed, now running program...\n")
    interpreter(parsed)


def script(name):
    main(name, True)
    reset_all()


def script_debug(name):
    global debug
    debug = True
    main(name, True)
    reset_all()


def from_input(s):
    main(s)
    reset_all()

def from_input_debug(s):
    global debug
    debug = True
    main(s)
    reset_all()

if __name__ == '__main__':
    from sys import argv
    if len(argv) == 2:
        script(argv[1])





             
        












