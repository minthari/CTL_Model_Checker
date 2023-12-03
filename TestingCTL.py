#Testing CTL
#The code defines classes and functions for working with logical expressions in Computation Tree Logic (CTL).
#CTL is a branching-time temporal logic that allows reasoning about the possible future states of a system.

#The code appears to be a comprehensive framework for performing CTL model checking on a given transition system with
# specified labels and formulas, while also providing visualization options to understand the results more effectively.

#The code defines two main types of operations: binary operations (BinOP) and unary operations (UOP).
#Binary operations include And, Or, and Implies, while unary operations include Not, EX, EU, AU, AX, AG, EG, AF, and EF.
#EU,AU and EX are the minimalist sets in CTL

#The main objective of the code is to determine whether the CTL formula(φ) is valid in the finite CTL model(S,R,label)


# φ::= x |¬φ | φ∧ψ | ∋0φ | ∋[φ⋃ψ] | ∀[φ⋃ψ]

from nfa import *
import toolkit
from nfa import NFA

NFA.clear()

from dataclasses import dataclass
@dataclass
class TRUE:
    symb = "T"

T = TRUE()
@dataclass
class FALSE:
    symb = "F"

# Define classes for binary operators (And, Or, Implies, AU, EU, Equivalence)
@dataclass
class BinOP:
    l:object
    r:object

class And(BinOP):
    symb = "&"

class Or(BinOP):
    symb = "|"

class Implies(BinOP):
    symb = "=>"

class AU(BinOP):
    symb = "AU"

class EU(BinOP):
    symb = "EU"

class Equivalence(BinOP):
    symb = "<=>"

## Define classes for unary operators (Not, EX, AX, AG, EG, AF, EF)
@dataclass
class UOP:
    f: object
class Not(UOP):
    symb = "-"
class EX(UOP):
    symb = "EX"
class AX(UOP):
    symb = "AX"
class AG(UOP):
    symb = "AG"
class EG(UOP):
    symb = "EG"
class AF(UOP):
    symb = "AF"
class EF(UOP):
    symb = "EF"

#recursively converts a CTL formula to a string.
def fstr(f):
    #print("fstr", f)
    match f:
        case TRUE() | FALSE(): return f.symb
        case str():
            return f
        case UOP(x):
            return f"{f.symb}{fstr(x)}"
        case BinOP(l, r):
            return f"({fstr(l)} {f.symb} {fstr(r)})"
        case _:
            raise ValueError(f)

# Add a function to implement the simplifications
def simplify(f):
    z = simplify
    match f:
        case EF(x):
            return EU(T, z(x))
        case AF(x):
            return AU(T, z(x))
        case EG(x):
            return Not(AF(Not(z(x))))
        case AG(x):
            return Not(EF(Not(z(x))))
        case AX(x):
            return Not(EX(Not(z(x))))
        case Implies(l, r):
            return Or(Not(z(l)), z(r))
        case Equivalence(l, r):
            return And(Implies(z(l), z(r)), Implies(z(r), z(l))) # (operator, left operand, right operand)
        case BinOP(l, r):
            return type(f)(z(l), z(r))
        case UOP(x):
            return type(f)(z(x))
        case _:
            return f

def fixpoint(f):
    def ff(x):
        r = f(x)
        #print(r)
        if x == r: return x
        return ff(r)
    return ff
simplify2 = fixpoint(simplify)
#def f(x): return x//2
#print(fixpoint(f)(4))

#Main function for model checking
# Define the data structures
class Formula:
    pass

class State:
    pass

class Label:
    pass

# Main function for model checking
#The purpose of this function is to evaluate the CTL formula and determine which states in the transition system satisfy the formula.
def Sat(φ, A, Label):
    for q in A.Q - Label.keys():
        Label[q]=set()
    R = { (p,q) for p,_,q in A.Δ }
    #print("Sat", φ)
    result = None
    match φ:
        case TRUE():
            return A.Q
            #result = A.Q
        case FALSE():
            return set()
        case str():
            return {q for q in A.Q if φ in Label[q]}
        case Not(φ):
            return A.Q - Sat(φ, A, Label)
        case Or(φ1, φ2):
            return Sat(φ1, A, Label) | Sat(φ2, A, Label)
        case And(φ1, φ2):
            return Sat(φ1, A, Label) & Sat(φ2, A, Label)
        case EX(φ):
            return { s for (s, ss) in R if ss in Sat(φ,A, Label) }
        case EU(φ1, φ2):
            return SatEU(φ1, φ2, A, Label)
        case AU(φ1, φ2):
            return SatAU(φ1, φ2, A, Label)
        case _:
            raise ValueError(φ)

    #print("Sat", φ, "Result:", result)
    #return result  # Return the result

# Define a function for the AU operator
def SatAU(φ, ψ, A, Label):
    Q, Q_ = Sat(ψ, A, Label), set()
    while Q != Q_:
        Q_ = Q.copy()
        #Q |= {s for (s, _, ss) in A.Δ if ss in Q} & Sat(φ, A, Label) #SatEU
        #Q |= {s for (s, _, ss) in A.Δ if all(ss in Q for (_, _, sss) in A.Δ if s == sss)} & Sat(φ, A, Label)
        Q |= {s for (s, _, ss) in A.Δ if all(ss in Q for (sss, _, _) in A.Δ if s == sss)} & Sat(φ, A, Label)
        #print(A.Δ)
    #print("Result:", Q)
    return Q

#Define a function for the EU operator
def SatEU(φ, ψ, A, Label):
    Q, Q_ = Sat(ψ, A, Label), set()
    #print("EU", Q, Q_)

    while Q != Q_:
        Q_ = Q.copy()
        #print(A.Δ)
        Q |= { s for (s, _, ss) in A.Δ if ss in Q } & Sat(φ, A, Label)
        #print("EU", Q, Q_)
        #print(Q)
    return Q

# Create an NFA object from a specification
A = NFA.spec("""
    0
    __
    0 1 2
    1 0 3
    2 1
    3 3
    """, name="Sample NFA",style="ts").visu()

p,q,r = "pqr"

# Define a dictionary for labels
labels = { 0: {p}, 1:{p,q}, 2:{q,r}, 3:{p} }

#Printing the result
Sat_old = Sat
def Sat(*a):
    #print(r := Sat_old(*a))
    return Sat_old(*a)

#-------------------------------------Example usage:Test cases----------------------------------------------------------
#f = And(Or(Not("A"), And(Implies("B", "C"), Implies("C", "B"))), Or(Not("D"), "E"))
#f = And(Or(Not(And("A", Equivalence("B", "C"))), Or(Not(Implies("D", "E")), And(Not("F"), EU("G", "H")))), And(AX(AF("I")), EG(Or(And(Not(Implies("J", "K")), EU("L", AG("M"))), And(EF("N"), AU(Or("O", EG("P")), Equivalence("Q", Not("R"))))))))
#f = Or(And(Not(AX(Or("A", "B"))), EU(EG("C"), AG(Not("D")))),And(Not(EF(Implies("E", "F"))), AG(AU("G", EF("H")))))
#f = Or(And(EX(Or("A", Not("B"))), AU(EG("C"), EF("D"))), And(Not(EG(Implies("E", "F"))), AF(AU("G", EF("H")))))
#f = And(Or(Not(AX(AU("A", "B"))), AU(EG(Implies("C", "D")), EF(Or("E", "F")))), And(Not(EG(Or("G", "H"))), AG(EU("I", Equivalence("J", "K")))))
#f = And(EX(Or("A", Not("B")), EU(EG("C"), EF("D"))), AF(AU("G", EF("H"))))
#f = Or(And(EX(Or("X", Not("Y"))), AU(EG("Z"), EF("W"))),And(Not(EG(Implies("M", "N"))), AF(AU("O", EF("P")))))
#f = And(EX(Not("P")), AF(EU(Not("P"), "Q")))
#f = And(AX(Or("P", EX("Q"))), EG(Or(Not("R"), "S")))
#f = Or(EX(EX(Not("P"))), EG(EU("Q", Not("R"))))
#f = EF(Not("S"))
#f = Or("X", "Y")

#-------------------------------- Assertion for Simplify----------------------------------------------------------------
"""assert simplify(EF("p")) == EU(TRUE(), "p")#EU(True, x)
assert simplify(AF("q")) == AU(TRUE(), "q")#AU(True, x)
assert simplify(EG("p")) == Not(AF(Not("p"))) #Not(AF(Not(x)))
assert simplify(AG("q")) == Not(EF(Not("q"))) #Not(EF(Not(x)))
assert simplify(AX("p")) == Not(EX(Not("p"))) #Not(EX(Not(x)))
assert simplify(Implies("p", "q")) == Or(Not("p"), "q") #Or(Not(l), r)
assert simplify(Equivalence("p", "q")) == And(Implies("p", "q"), Implies("q", "p")) #And(Implies(l, r), Implies(r, l))
assert simplify(Or("p", And("q", "r"))) == Or("p", And("q", "r"))
assert simplify(Not("p")) == Not("p")
assert simplify("p") == "p"
assert simplify(AG("p")) == Not(EF(Not("p")))
assert simplify(AX(TRUE())) == Not(EX(Not(TRUE()))) # AXφ=¬EX¬φ"""

#-------------------------------- Assertion for Sat---------------------------------------------------------------------
"""assert Sat(TRUE(), A, labels) == A.Q  # TRUE returns all states
assert Sat(FALSE(), A, labels) == set()  # FALSE returns an empty set
assert Sat("p", A, labels) == {0, 1, 3}  # Atomic proposition "p" is in states 0, 1, and 3
assert Sat("r", A, labels) == set()  # Atomic proposition "r" is not in any state
assert Sat(Not("p"), A, labels) == {2}  # Negation of "p" is in state 2
assert Sat(Or("p", "q"), A, labels) == {0, 1, 2, 3}  # OR of "p" and "q" is in all states"""

#----------------------------- Test for Sat(φ, A, Label) - EX case------------------------------------------------------
"""assert Sat(EX(TRUE()), A, labels) == {0, 1, 2, 3}
assert Sat(EX(FALSE()), A, labels) == set()
assert Sat(EX("p"), A, labels) == {0, 1, 2, 3}
assert Sat(EX(Or("p", "q")), A, labels) == {0, 1, 2, 3}
assert Sat(EX(Not("p")), A, labels) == {0}
#assert Sat(AX("p"), A, labels) == {1, 2, 3}"""

#----------------------------------- Test for Sat(φ, A, Label) - Or case------------------------------------------------
"""assert Sat(Or(TRUE(), TRUE()), A, labels) == A.Q
assert Sat(Or(FALSE(), FALSE()), A, labels) == set()
assert Sat(Or("p", "q"), A, labels) == {0, 1, 2, 3}"""

#------------------------------------- Assertion for SatEU--------------------------------------------------------------

assert (x := SatEU("p", "q", A, labels)) == {0, 1, 2}, x  # EF(p U q) is satisfied in all states
assert SatEU(TRUE(), TRUE(), A, labels) == A.Q  # SatEU(TRUE, TRUE) = all states
assert SatEU(TRUE(), FALSE(), A, labels) == set()  # SatEU(TRUE, FALSE) = no states
assert SatEU(TRUE(), "q", A, labels) == {0,1,2}  # TRUE EU q
assert SatEU("p", "q", A, labels) == {0, 1, 2}  # SatEU(p, q) = all states 
assert SatEU(EX("p"), "q", A, labels) == {0, 1, 2}  # SatEU(EX(p), q) 
assert SatEU(EX("p"), TRUE(), A, labels) == {0, 1, 2, 3}  # EX(p) EU TRUE is satisfied in all states
assert SatEU(EX(EX("p")), "q", A, labels) == {0, 1, 2}  # SatEU(EX(EX(p)), q) 
assert SatEU(EX("p"), EX("q"), A, labels) == {0, 1, 2}  # SatEU(EX(p), EX(q))
assert SatEU(EX(EX("p")), EX(EX("q")), A, labels) == {0, 1, 2}  # SatEU(EX(EX(p)), EX(EX(q)))
assert SatEU(EX(Or("p", "q")), EX("p"), A, labels) == {0, 1, 2, 3}  # SatEU(EX(p OR q), EX(p)) = all states
assert SatEU(EX(EX(EX(Or("p", "q")))), EX(EX(EX("p"))), A, labels) == {0, 1, 2, 3}  # Complex SatEU assertion """
assert SatEU("p", TRUE(), A, labels) == {0, 1, 2, 3}  # SatEU(p, TRUE) = states 0, 1, 3

#---------------------------------------- Assertion for SatAU-----------------------------------------------------------
assert SatAU(TRUE(), TRUE(), A, labels) == A.Q  # SatAU(TRUE, TRUE) = all states
assert SatAU(TRUE(), FALSE(), A, labels) == set()  # SatAU(TRUE, FALSE) = no states
assert SatAU("p", TRUE(), A, labels) == {0, 1, 2, 3}  # SatAU(p, TRUE) = states 0, 1, 3"""
assert SatAU("p", "q", A, labels) == {0,1,2}  # SatAU(p, q)
assert SatAU(EX("p"), "q", A, labels) == {0, 1, 2}  # SatAU(EX(p), q) = all states
assert SatAU(EX(EX("p")), "q", A, labels) == {0, 1, 2}  # SatAU(EX(EX(p)), q) = all states
assert SatAU(EX("p"), EX("q"), A, labels) == {0, 1, 2}  # SatAU(EX(p), EX(q)) = all states

assert SatAU(EX(EX("p")), EX(EX("q")), A, labels) == {0, 1, 2}  # SatAU(EX(EX(p)), EX(EX(q))) = all states
assert SatAU(EX(Or("p", "q")), EX("p"), A, labels) == {0, 1, 2,3}  # SatAU(EX(p OR q), EX(p)) = all states
assert SatAU(EX(EX(EX(Or("p", "q")))), EX(EX(EX("p"))), A, labels) == {0, 1, 2, 3}  # Complex SatAU assertion
assert SatAU(EX("q"), TRUE(), A, labels) == {0, 1, 2, 3}  # EX(q) U TRUE is satisfied in all states
assert SatAU(EX("p"), "q", A, labels) == {0,1,2}  # EX(p) U q is not satisfied in any state"""

#---------------------------------------- Assertion for Sat-----------------------------------------------------------
# Assertions for EU operator
assert Sat(EU("p", "q"), A, labels) == {0, 1, 2}
assert Sat(EU(TRUE(), TRUE()), A, labels) == A.Q
assert Sat(EU(TRUE(), FALSE()), A, labels) == set()
assert Sat(EU(TRUE(), "q"), A, labels) == {0, 1, 2}
assert Sat(EU("p", "q"), A, labels) == {0, 1, 2}
assert Sat(EU(EX("p"), "q"), A, labels) == {0, 1, 2}
assert Sat(EU(EX("p"), TRUE()), A, labels) == {0, 1, 2, 3}
assert Sat(EU(EX(EX("p")), "q"), A, labels) == {0, 1, 2}
assert Sat(EU(EX("p"), EX("q")), A, labels) == {0, 1, 2}
assert Sat(EU(EX(EX("p")), EX(EX("q"))), A, labels) == {0, 1, 2}
assert Sat(EU(EX(Or("p", "q")), EX("p")), A, labels) == {0, 1, 2, 3}
assert Sat(EU(EX(EX(EX(Or("p", "q")))), EX(EX(EX("p")))), A, labels) == {0, 1, 2, 3}
assert Sat(EU("p", TRUE()), A, labels) == {0, 1, 2, 3}

# Assertions for AU operator
assert Sat(AU(TRUE(), TRUE()), A, labels) == A.Q
assert Sat(AU(TRUE(), FALSE()), A, labels) == set()
assert Sat(AU("p", TRUE()), A, labels) == {0, 1, 2, 3}
assert Sat(AU("p", "q"), A, labels) == {0, 1, 2}
assert Sat(AU(EX("p"), "q"), A, labels) == {0, 1, 2}
assert Sat(AU(EX(EX("p")), "q"), A, labels) == {0, 1, 2}
assert Sat(AU(EX("p"), EX("q")), A, labels) == {0, 1, 2}

# Mix of different sub-formulas in Sat function
assert Sat(AU("p", EU("q", "p")), A, labels) == {0, 1, 2, 3}  # For all paths, "p" holds until there exists a path where "q" until "p"
assert Sat(EU(EX("p"), AU(EX("q"), "p")), A, labels) == {0, 1, 2, 3}
assert Sat(AU(EX(EX("p")), "q"), A, labels) == {0, 1, 2}
assert Sat(EU(EX("p"), AU(EX(EX("p")), EX(EX("q")))), A, labels) == {0, 1, 2}
assert Sat(AU(EX("p"), EU(EX("q"), EX(EX("p")))), A, labels) == {0, 1, 2, 3}
assert Sat(EU(EX(EX(EX("p"))), AU(EX(EX("p")), EX(EX("q")))), A, labels) == {0, 1, 2}
assert Sat(AU(Not(EX("p")), EX(EX("q"))), A, labels) == {0, 1}  # For all paths, negation of in the next state, "p" holds until in the next state, in the next state, "q" holds

#-----------------------------------------------------------------------------------------------------------------------

"""f_simplified = fstr(simplify(simplify(f)))
print(fstr(f))
#print(fstr(simplify(f)))
#print(fstr(simplify(simplify(f))))
print(fstr(simplify2(f)))"""

# Simplify the formulas
#f_simplified = simplify(f)
#assert Sat(f_simplified, A, labels) == {0,1, 2, 3}

# Use the simplified formulas for the main algorithm
#result = Sat(f_simplified, A, labels)
#result = Sat(f_simplified, A, label_dict)
#print(result)"""


#---------------------------------------Visualization ------------------------------------------------------------------
def subs(f):
    if fstr(f): return {f}
    return {f} | set.union(*(subs(φ) for φ in f[1:] ))

def f_len(f):
    if fstr(f): return 1
    return 1+max(f_len(φ) for φ in f[1:])

def sortsubs(f):
    return sorted(subs(f), key=f_len)

ATOMS = "atoms"
SIMPLE = "simple"
CHECKVISU = (SIMPLE,)
def checkvisu(A,l,f,visu=None):
    N = A.name

    visu = visu if visu is not None else CHECKVISU
    if ATOMS in visu:
        n = f"{N} : {fstr(f)}: atoms"
        A.label(l,fstr).named(n).visu(
            node_shape="box",epsilon_style="",size=False,break_strings=False)

    print("Expression", f)
    f = simplify2(f)
    print(f, fstr(f))
    res = Sat(f,A,l)
    print(res)

    if SIMPLE in visu:
        dmod = { q:
                 'color="#00BB00" fillcolor="#00FF00" penwidth=2 fontcolor=white'
                 if q in res else
                 'color="#770000" fillcolor="#BB0000" penwidth=2 fontcolor=white'
                 for q in l }
        n = f"{N} : {fstr(f)}: simple"
        A.named(n).visu(dmod=dmod,epsilon_style="",size=False)

    A.name = N


#f = Not(p) # {2}
#f = (p) # {0, 1, 3}
#f = AG(p) #{1, 3} | Not(EF(Not("p")))

# f = And(EX(Not("p")), AF(EU(Not("p"), "q")))
checkvisu(A, labels , p, visu=(ATOMS,))
"""for f in [
    p,
    Not(p),
    TRUE(),
    #EU(TRUE(), Not(p)),
    EU(TRUE(), r),
    AG(p)
]: """

#f = AU("A", EG(Not("B")))
#f = EU(AF("A"), EG(EX("B")))
#f = AU(EX(Or("A", "B")), "C")
f = Sat(AU(EG("p"), EX(AU("q", "r"))), A, labels)
checkvisu(A, labels , f)


