module ToMockAMockingbird

%default total 

interface Bird b where 
    ||| A <*> B is A's response to B
    (<*>) : b -> b -> b

%hint 
sym2 : (0 _ : x = y) -> y = x
sym2 = sym
%hint 
trans2 : (0 _ : a = b) -> (0 _ : b = c) -> a = c
trans2 = trans

parameters {b : Type} {auto _ : Bird b}
    Mockingbird : b -> Type
    Mockingbird m = (x : b) -> m <*> x = x <*> x

    Composition : b -> b -> b -> Type 
    Composition xA xB xC = (x : b) -> xC <*> x = xA <*> (xB <*> x)

    Fond : b -> b -> Type 
    Fond xA xB = xA <*> xB = xB 


    Condition1 : Type 
    Condition1 = (xA : b) -> (xB : b) -> (xC ** Composition xA xB xC)

    Condition2 : Type 
    Condition2 = (m ** Mockingbird m)

    question1 : Condition1 -> Condition2 -> (x : b) -> (y ** Fond x y)
    question1 c1 (m**mock) xA = 
        let (xC**prf) = c1 xA m
            eq1 = prf xC
            eq2 = mock xC
        in (m <*> xC ** %search)
    --A(CC) = A(MC) 
    --CC = A(MC)    -> eq1

    Egocentric : b -> Type 
    Egocentric x = x <*> x = x

    question2 : Condition1 -> Condition2 -> (xE ** Egocentric xE)
    question2 c1 c2@(m**mock) = 
        let (xE**eq1) = question1 c1 c2 m
            eq2 = mock xE
        in (xE ** %search)
    --ME = E    -> eq1
    --ME = EE   -> eq2
    
    Agree : b -> b -> b -> Type 
    Agree xA xB x = xA <*> x = xB <*> x

    Agreeable : b -> Type 
    Agreeable xA = (xB : b) -> (x ** Agree xA xB x)


    question3 : Condition1 -> (xA : b) -> (Agreeable xA) -> (x : b) -> (y ** Fond x y)
    question3 c1 xA aggreable x = 
        let (xH**prf) = c1 x xA
            (y**eq1) = aggreable xH
            eq2 = prf y
        in (xA <*> y ** %search)
    --Hy = x(Ay)    eq2
    --Ay = Hy       eq1

    question4 : Condition1 -> (xA : b) -> (xB : b) -> (xC : b) -> (Composition xA xB xC) -> (Agreeable xC) -> Agreeable xA
    question4 c1 xA xB xC comp aggreable xD = 
        let (xE**prf) = c1 xD xB
            (x**eq1) = aggreable xE
            eq2 = prf x
            eq3 = comp x
        in (xB <*> x ** %search)
    --Ex = D(Bx)    eq2
    --Cx = Ex       eq1
    --Cx = A(Bx)    eq3

    TripleComposition : b -> b -> b -> b -> Type 
    TripleComposition xA xB xC xD = (x : b) -> xD <*> x = xA <*> (xB <*> (xC <*> x))

    question5 : Condition1 -> (xA : b) -> (xB : b) -> (xC : b) -> (xD ** TripleComposition xA xB xC xD)
    question5 c1 xA xB xC = 
        let (xAB**prf1) = c1 xA xB
            (xABC**prf2) = c1 xAB xC
        in (xABC ** \x => 
            let eq1 = prf1 (xC <*> x)
                eq2 = prf2 x
            in %search)
    
    