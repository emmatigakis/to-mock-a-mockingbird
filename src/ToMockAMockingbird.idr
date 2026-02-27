module ToMockAMockingbird

%default total 

public export
interface Bird b where 
    ||| A <*> B is A's response to B
    (<*>) : b -> b -> b

public export
data Compatible : {auto b : _} -> Bird b => b -> b -> Type where
    MkCompatible : {b : _} -> Bird b => {xA : b} -> {xB : b} -> (x : b) -> (y : b) -> (xA <*> x = y) -> (xB <*> y = x) -> Compatible xA xB

public export
data Normal : {auto b : _} -> Bird b => b -> Type where
    IsNormal : {b : _} -> Bird b => {xA : b} -> (x : b) -> (xA <*> x = x) -> Normal xA

parameters {auto b : Type} {auto _ : Bird b}
    public export
    Mockingbird : b -> Type
    Mockingbird m = (x : b) -> m <*> x = x <*> x

    public export
    Composition : b -> b -> b -> Type 
    Composition xA xB xC = (x : b) -> xC <*> x = xA <*> (xB <*> x)

    public export
    Fond : b -> b -> Type 
    Fond xA xB = xA <*> xB = xB 

    public export
    Condition1 : Type 
    Condition1 = (xA : b) -> (xB : b) -> (xC ** Composition xA xB xC)

    public export
    Condition2 : Type 
    Condition2 = (m ** Mockingbird m)

    export
    question1 : Condition1 -> Condition2 -> (x : b) -> (y ** Fond x y)
    question1 c1 (m**mock) xA = 
        let (xC**prf) = c1 xA m
            eq1 = prf xC
            eq2 = mock xC
        in (m <*> xC ** sym $ trans eq2 eq1)
    --A(CC) = A(MC) 
    --CC = A(MC)    -> eq1

    public export
    Egocentric : b -> Type 
    Egocentric x = x <*> x = x

    export
    question2 : Condition1 -> Condition2 -> (xE ** Egocentric xE)
    question2 c1 c2@(m**mock) = 
        let (xE**eq1) = question1 c1 c2 m
            eq2 = mock xE
        in (xE ** trans (sym eq2) eq1)
    --ME = E    -> eq1
    --ME = EE   -> eq2
    
    public export
    Agree : b -> b -> b -> Type 
    Agree xA xB x = xA <*> x = xB <*> x

    public export
    Agreeable : b -> Type 
    Agreeable xA = (xB : b) -> (x ** Agree xA xB x)

    export
    question3 : Condition1 -> (xA : b) -> (Agreeable xA) -> (x : b) -> (y ** Fond x y)
    question3 c1 xA aggreable x = 
        let (xH**prf) = c1 x xA
            (y**eq1) = aggreable xH
            eq2 = prf y
        in (xA <*> y ** sym $ trans eq1 eq2)
    --Hy = x(Ay)    eq2
    --Ay = Hy       eq1

    export
    question4 : Condition1 -> (xA : b) -> (xB : b) -> (xC : b) -> (Composition xA xB xC) -> (Agreeable xC) -> Agreeable xA
    question4 c1 xA xB xC comp aggreable xD = 
        let (xE**prf) = c1 xD xB
            (x**eq1) = aggreable xE
            eq2 = prf x
            eq3 = comp x
        in (xB <*> x ** trans (sym eq3) $ trans eq1 eq2)
    --Ex = D(Bx)    eq2
    --Cx = Ex       eq1
    --Cx = A(Bx)    eq3

    public export
    TripleComposition : b -> b -> b -> b -> Type 
    TripleComposition xA xB xC xD = (x : b) -> xD <*> x = xA <*> (xB <*> (xC <*> x))

    export
    question5 : Condition1 -> (xA : b) -> (xB : b) -> (xC : b) -> (xD ** TripleComposition xA xB xC xD)
    question5 c1 xA xB xC = 
        let (xAB**prf1) = c1 xA xB
            (xABC**prf2) = c1 xAB xC
        in (xABC ** \x => 
            let eq1 = prf1 (xC <*> x)
                eq2 = prf2 x
            in trans eq2 eq1)
        
    export
    question6 : Condition1 -> Condition2 -> (xA : b) -> (xB : b) -> Compatible xA xB
    question6 c1 c2 xA xB = 
        let (xC**prf) = c1 xA xB
            (y**eq1) = question1 c1 c2 xC
            eq2 = prf y
        in MkCompatible (xB <*> y) y (trans (sym eq2) eq1) Refl
    --Cy = A(By)    eq2
    --Cy = y        eq1
    --x = By

    public export
    Happy : b -> Type 
    Happy xA = Compatible xA xA 

    export
    question7 : (xA : b) -> (x : b) -> (Fond xA x) -> Happy xA
    question7 xA x prf = 
        MkCompatible x x prf prf
    --Ax = x
    
    export
    question8 : {xH : b} -> Condition1 -> Happy xH -> (xB ** Normal xB)
    question8 c1 (MkCompatible x y eq1 eq2) = 
        let (xB**prf) = c1 xH xH
            eq3 = prf y
        in (xB ** IsNormal y (rewrite eq3 in rewrite eq2 in eq1))
    --Hx = y    eq1
    --Hy = x    eq2
    --H(Hy) = y
    --By = H(Hy)    eq3 

    public export
    Fixated : b -> b -> Type 
    Fixated xA xB = (x : b) -> xA <*> x = xB

    public export
    HopelesslyEgocentric : b -> Type 
    HopelesslyEgocentric xB = Fixated xB xB

    public export
    Kestrel : b -> Type  
    Kestrel xK = (x : b) -> (y : b) -> (xK <*> x) <*> y = x

    export
    question9 : Condition1 -> Condition2 -> {xK : b} -> Kestrel xK -> (xA ** HopelesslyEgocentric xA)
    question9 c1 c2 kestrel = 
        let (xA**eq1) = question1 c1 c2 xK
        in (xA ** \x => let eq2 = kestrel xA x in rewrite sym eq1 in sym $ trans eq1 $ sym eq2)
    --KA = A        eq1 
    --(KA)x = Ax
    --(KA)x = A     eq2 

    export
    question10 : {y : b} -> Fixated x y -> Fond x y
    question10 f = f y
    
    export
    question11 : {xK : b} ->  Kestrel xK -> Egocentric xK -> HopelesslyEgocentric xK
    question11 kestrel ego z = 
        let eq1 = kestrel xK z 
        in rewrite sym ego in sym $ trans ego $ sym eq1

    export
    question12 : {xK : b} -> {x : b} -> Kestrel xK -> (x : b) -> Egocentric (xK <*> x) -> Fond xK x
    question12 kestrel x eq1 = 
        let eq2 = kestrel x (xK <*> x)
        in trans (sym eq1) eq2
    --(Kx)(Kx) = Kx eq1
    --(Kx)(Kx) = x  eq2

    export
    question13 : {xA : b} -> HopelesslyEgocentric xA -> (x : b) -> (y : b) -> xA <*> x = xA <*> y
    question13 prf x y = 
        let eq1 = prf x
            eq2 = prf y
        in sym $ trans eq2 $ sym eq1
    
    export
    question14 : {xA : b} -> HopelesslyEgocentric xA -> (x : b) -> (y : b) -> (xA <*> x) <*> y = xA
    question14 prf x y = 
        rewrite prf x in prf y
    
    export
    question15 : {xA : b} -> HopelesslyEgocentric xA -> (x : b) -> HopelesslyEgocentric (xA <*> x)
    question15 prf x y = 
        let eq1 = question14 prf x y
            eq2 = prf x
        in sym $ trans eq2 $ sym eq1
    --(Ax)y = A eq1
    --Ax = A
    --(Ax)y = Ax

    export
    question16 : {xK : b} -> Kestrel xK -> (x : b) -> (y : b) -> xK <*> x = xK <*> y -> x = y
    question16 kestrel x y eq1 = 
        let eq2 = kestrel x xK
            eq3 = kestrel y xK
        in rewrite sym eq2 in rewrite sym eq3 in cong (<*> xK) eq1
    --Kx = Ky  eq1
    --(Kx)z = (Ky)z
    --(Kx)z = x eq2 z=K
    --(Ky)z = y eq3 z=K

    export
    question17 : {xA : b} -> Fixated xA x -> Fixated xA y -> x = y
    question17 prf1 prf2 = 
        let eq1 = prf1 xA
            eq2 = prf2 xA
        in trans (sym eq1) eq2
    --Az = y
    --Az = x

    export
    question18 : {xK : b} -> Kestrel xK -> (x : b) -> Fond xK (xK <*> x) -> Fond xK x
    question18 kestrel x eq1 = question16 kestrel (xK <*> x) x eq1
    --K(Kx) = Kx

    export
    question19 : {xK : b} -> Kestrel xK -> Egocentric xK -> (x : b) -> x = xK
    question19 kestrel ego x = 
        let prf = question11 kestrel ego x
        in question16 kestrel x xK $ sym $ trans ego $ sym prf
        --Kx = K
        --Ky = K
        --Kx = Ky

    public export
    Identity : b -> Type 
    Identity xI = (x : b) -> xI <*> x = x

    export
    question20 : {xI : b} -> Identity xI -> Agreeable xI -> (x : b) -> (y ** Fond x y)
    question20 prf1 prf2 x = 
        let (y**eq1) = prf2 x
            eq2 = prf1 y
        in (y ** trans (sym eq1) eq2)
    --xy = Iy = y

    export
    question21 : {xI : b} -> Identity xI -> ((x : b) -> (y ** Fond x y)) -> Agreeable xI
    question21 prf1 prf2 x = 
        let (y ** eq1) = prf2 x
            eq2 = prf1 y
        in (y ** sym $ trans eq1 $ sym eq2)
    --xy = y = Iy

    export
    question22a : {xI : b} -> Identity xI -> ((x : b) -> (y : b) -> Compatible x y) -> (xB : b) -> Normal xB
    question22a prf1 prf2 xB = --?tmp
        let (MkCompatible x y eq1 eq2) = prf2 xB xI 
            eq3 = prf1 y
        in IsNormal x $ trans eq1 $ trans (sym eq3) eq2 
    --Bx = y
    --Iy = x
    --y = x
    --Bx = x

    export
    question22b : {xI : b} -> Identity xI -> ((x : b) -> (y : b) -> Compatible x y) -> Agreeable xI
    question22b prf1 prf2 xB =
        question21 prf1 (\x => let IsNormal y prf3 = question22a prf1 prf2 x in (y ** prf3)) xB

    export
    question23 : {xI : b} -> Identity xI -> HopelesslyEgocentric xI -> (x : b) -> x = xI
    question23 prf1 prf2 x = 
        let eq1 = prf1 x
            eq2 = prf2 x
        in trans (sym eq1) eq2
    --Ix = I    eq2
    --Ix = x    eq1 

    public export
    Lark : b -> Type 
    Lark xL = (x : b) -> (y : b) -> (xL <*> x) <*> y = x <*> (y <*> y)

    export
    question24 : {xL : b} -> {xI : b} -> Lark xL -> Identity xI -> (m ** Mockingbird m)
    question24 lark ident = 
        (xL <*> xI ** \x => 
            let eq1 = ident (x <*> x)
                eq2 = lark xI x
            in trans eq2 eq1)
    --(LI)x = I(xx) = xx

    export
    lark_lemma : {xL : b} -> Lark xL -> (x : b) -> Fond x ((xL <*> x)<*>(xL <*> x))
    lark_lemma lark x = 
        sym $ lark x (xL <*> x)
        
    export
    question25 : {xL : b} -> Lark xL -> (x : b) -> Happy x
    question25 lark x = 
        question7 x ((xL <*> x)<*>(xL <*> x)) $ lark_lemma lark x
    --(Lx)(Lx) = x((Lx)(Lx))

    export
    question26 : {xL : b} -> Lark xL -> HopelesslyEgocentric xL -> (x : b) -> Fond x xL
    question26 lark ego x = 
        let eq1 = question14 ego x (xL <*> x)
            eq2 = lark_lemma lark x
        in rewrite sym eq1 in eq2
    --(Lx)y = L q14
    --(Lx)(Lx) = L  eq1

    export
    question27 : ((x : b) -> Lark x -> Kestrel x -> Void) -> {xL : b} -> Lark xL -> (xK : b) -> Fond xL xK -> Not(Kestrel xK)
    question27 cond lark xK eq1 kestrel = 
        let eq2 = cong (<*> xK) eq1
            eq3 = lark xK xK
            eq4 = trans (sym eq3) eq2
            eq5 = question18 kestrel xK eq4 
            eq6 = question19 kestrel eq5 xL
        in cond xL lark (\x => \y => rewrite eq6 in kestrel x y)
        --LK = K        eq1
        --(LK)K = KK    eq2
        --(LK)K = K(KK) eq3

    export
    question28 : {xK : b} -> Kestrel xK -> {xL : b} -> Lark xL -> Fond xK xL -> (x : b) -> Fond x xL
    question28 kestrel lark fond  = 
        question26 lark (\x => rewrite sym fond 
            in let eq1 = kestrel xL x in 
            rewrite eq1 in sym fond) 
    

    export
    question29 : {xL : b} -> Lark xL -> (xE ** Egocentric xE)
    question29 lark = 
        let eq1 = lark_lemma lark (xL <*> xL)
            --l_ll = xL <*> (xL <*> xL)
            (l_ll**eq2) = the (l_ll ** l_ll = xL <*> (xL <*> xL)) (xL <*> (xL <*> xL) ** Refl)
            (y**eq3) = the (y ** y = (l_ll <*> l_ll)) (l_ll <*> l_ll ** Refl)
            eq4 = lark xL y
            eq5 = the ((xL <*> xL) <*> y = y) (rewrite eq3 in sym $ rewrite eq3 in rewrite eq2 in sym eq1)
            eq6 = trans (sym eq4) eq5
            eq7 = cong (<*> y) eq6 
            eq8 = lark (y <*> y) y
        in (y<*>y ** trans (sym eq8) eq7)
        --(LL)y = y         eq5 
        --(LL)y = L(yy)     eq4 
        --L(yy) = y         eq6 
        --L(yy)y = yy       eq7
        --L(yy)y = (yy)(yy) eq8

    %ambiguity_depth 5
    export 
    question29b : {xL : b} -> Lark xL -> (xE ** Egocentric xE)
    question29b lark = 
        (((xL<*>((xL<*>(xL<*>xL))<*>(xL<*>(xL<*>xL))))<*>(xL<*>(xL<*>xL))) ** 
        sym (trans (trans (trans (lark ((xL<*>(xL<*>xL))<*>(xL<*>(xL<*>xL))) (xL<*>(xL<*>xL))) (cong2 (<*>) (lark (xL<*>xL) (xL<*>(xL<*>xL))) (lark (xL<*>xL) (xL<*>(xL<*>xL))))) (cong2 (<*>) (lark (xL) ((xL<*>(xL<*>xL))<*>(xL<*>(xL<*>xL)))) (sym (lark (xL<*>xL) (xL<*>(xL<*>xL)))))) (sym (trans (cong2 (<*>) (lark ((xL<*>(xL<*>xL))<*>(xL<*>(xL<*>xL))) (xL<*>(xL<*>xL))) (lark ((xL<*>(xL<*>xL))<*>(xL<*>(xL<*>xL))) (xL<*>(xL<*>xL)))) (sym (lark (((xL<*>(xL<*>xL))<*>(xL<*>(xL<*>xL)))<*>((xL<*>(xL<*>xL))<*>(xL<*>(xL<*>xL)))) ((xL<*>(xL<*>xL))<*>(xL<*>(xL<*>xL)))))))))