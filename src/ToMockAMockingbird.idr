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
    
    data Compatible : b -> b -> Type where
        MkCompatible : (x : b) -> (y : b) -> (xA <*> x = y) -> (xB <*> y = x) -> Compatible xA xB
    
    question6 : Condition1 -> Condition2 -> (xA : b) -> (xB : b) -> Compatible xA xB
    question6 c1 c2 xA xB = 
        let (xC**prf) = c1 xA xB
            (y**eq1) = question1 c1 c2 xC
            eq2 = prf y
        in MkCompatible (xB <*> y) y %search Refl
    --Cy = A(By)    eq2
    --Cy = y        eq1
    --x = By

    Happy : b -> Type 
    Happy xA = Compatible xA xA 

    question7 : (xA : b) -> (x : b) -> (Fond xA x) -> Happy xA
    question7 xA x prf = 
        MkCompatible x x prf prf
    --Ax = x
    
    data Normal : b -> Type where
        IsNormal : (x : b) -> (Fond xA x) -> Normal xA

    question8 : {xH : b} -> Condition1 -> Happy xH -> (xB ** Normal xB)
    question8 c1 (MkCompatible x y eq1 eq2) = 
        let (xB**prf) = c1 xH xH
            eq3 = prf y
        in (xB ** IsNormal y (rewrite eq3 in rewrite eq2 in eq1))
    --Hx = y    eq1
    --Hy = x    eq2
    --H(Hy) = y
    --By = H(Hy)    eq3 

    Fixated : b -> b -> Type 
    Fixated xA xB = (x : b) -> xA <*> x = xB

    HopelesslyEgocentric : b -> Type 
    HopelesslyEgocentric xB = Fixated xB xB

    Kestrel : b -> Type  
    Kestrel xK = (x : b) -> (y : b) -> (xK <*> x) <*> y = x

    question9 : Condition1 -> Condition2 -> {xK : b} -> Kestrel xK -> (xA ** HopelesslyEgocentric xA)
    question9 c1 c2 kestrel = 
        let (xA**eq1) = question1 c1 c2 xK
        in (xA ** \x => let eq2 = kestrel xA x in rewrite sym eq1 in %search)
    --KA = A        eq1 
    --(KA)x = Ax
    --(KA)x = A     eq2 

    question10 : {y : b} -> Fixated x y -> Fond x y
    question10 f = f y
    

    question12 : {xK : b} -> {x : b} -> Kestrel xK -> (x : b) -> Egocentric (xK <*> x) -> Fond xK x
    question12 kestrel x eq1 = 
        let eq2 = kestrel x (xK <*> x)
        in %search
    --(Kx)(Kx) = Kx eq1
    --(Kx)(Kx) = x  eq2

    question13 : {xA : b} -> HopelesslyEgocentric xA -> (x : b) -> (y : b) -> xA <*> x = xA <*> y
    question13 prf x y = 
        let eq1 = prf x
            eq2 = prf y
        in %search
    
    question14 : {xA : b} -> HopelesslyEgocentric xA -> (x : b) -> (y : b) -> (xA <*> x) <*> y = xA
    question14 prf x y = 
        rewrite prf x in prf y
    