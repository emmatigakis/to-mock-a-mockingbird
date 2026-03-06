module BirdsGalore

import ToMockAMockingbird

%default total 

%ambiguity_depth 8
data Dove : {auto b : _} -> Bird b => Type where 
    MkDove : {b : _} -> Bird b => (xD : b) -> ((x : b) -> (y : b) -> (z : b) -> (w : b) -> xD <*> x <*> y <*> z <*> w = x <*> y <*> (z <*> w)) -> Dove

data Blackbird : {auto b : _} -> Bird b => Type where
    MkBlackbird : {b : _} -> Bird b => (xB1 :b) -> ((x :b ) -> (y : b) -> (z : b) -> (w : b) -> xB1 <*> x <*> y <*> z <*> w = x <*> (y <*> z <*> w)) -> Blackbird

data Eagle : {auto b : _} -> Bird b => Type where
    MkEagle : {b : _} -> Bird b => (xE : b) -> ((x :b ) -> (y : b) -> (z : b) -> (w : b) -> (v : b) -> xE <*> x <*> y <*> z <*> w <*> v = x <*> y <*> (z <*> w <*> v)) -> Eagle

data Bunting : {auto b : _} -> Bird b => Type where
    MkBunting : {b : _} -> Bird b => (xB2 : b) -> ((x :b ) -> (y : b) -> (z : b) -> (w : b) -> (v : b) -> xB2 <*> x <*> y <*> z <*> w <*> v = x <*> (y <*> z <*> w <*> v)) -> Bunting

data Dickcissel : {auto b : _} -> Bird b => Type where
    MkDickcissel : {b : _} -> Bird b => (xD1 : b) -> 
        ((x :b ) -> (y : b) -> (z : b) -> (w : b) -> (v : b) -> xD1 <*> x <*> y <*> z <*> w <*> v = x <*> y <*> z <*> (w <*> v)) 
        -> Dickcissel

data Becard : {auto b : _} -> Bird b => Type where
    MkBecard : {b : _} -> Bird b => (xB3 : b) -> ((x :b ) -> (y : b) -> (z : b) -> (w : b) -> xB3 <*> x <*> y <*> z <*> w = x <*> (y <*>(z <*> w))) -> Becard

data Dovekie : {auto b : _} -> Bird b => Type where
    MkDovekie : {b : _} -> Bird b => (xD2 : b) -> 
        ((x :b ) -> (y : b) -> (z : b) -> (w : b) -> (v : b) -> xD2 <*> x <*> y <*> z <*> w <*> v = x <*> (y <*> z) <*> (w <*> v)) 
        -> Dovekie

data BaldEagle : {auto b : _} -> Bird b => Type where
    MkBaldEagle : {b : _} -> Bird b => (xBE : b) -> 
        ((x :b ) -> (y1 : b) -> (y2 : b) -> (y3 : b) -> (z1 : b) -> (z2 : b) -> (z3 : b) -> xBE <*> x <*> y1 <*> y2 <*> y3 <*> z1 <*> z2 <*> z3 = x <*> (y1 <*> y2 <*> y3) <*> (z1 <*> z2 <*> z3)) 
        -> BaldEagle

parameters {auto b : Type} {auto _ : Bird b}
    Bluebird : b -> Type
    Bluebird xB = (x : b) -> (y : b) -> (z : b) -> xB <*> x <*> y <*> z = x <*> (y <*> z)

    question1 : {xB : b} -> Bluebird xB -> Condition1
    question1 bluebird yA yB = 
        (xB <*> yA <*> yB ** bluebird yA yB)
    
    question2 : {xB : b} -> Bluebird xB -> (m : b) -> Mockingbird m -> (x : b) -> Fond x ((xB <*> x <*> m)<*>(xB <*> x <*> m))
    question2 bluebird m mock x = 
        let eq1 = sym $ bluebird x m ((xB <*> x) <*> m)
        in trans (cong (x <*>) $ sym $ mock ((xB <*> x) <*> m)) eq1
    
    question2b : {xB : b} -> Bluebird xB -> (m : b) -> Mockingbird m -> (x : b) -> Fond x (m<*>(xB <*> x <*> m))
    question2b bluebird m mock x = 
        let eq1 = question2 bluebird m mock x
            eq2 = cong (x<*>) $ mock ((xB <*> x) <*> m)
            eq3 = trans eq2 eq1
        in trans eq3 $ sym $ mock ((xB <*> x) <*> m)
    
    question3 : {xB : b} -> Bluebird xB -> (m : b) -> Mockingbird m -> Egocentric (m <*> (xB <*> m <*> m))
    question3 bluebird m mock = 
        let eq1 = question2b bluebird m mock m
        in trans (sym $ mock (m <*> ((xB <*> m) <*> m))) eq1
    
    question4 : 
        {xB : b} -> Bluebird xB -> 
        (m : b) -> Mockingbird m -> 
        (xK : b) -> Kestrel xK 
        -> HopelesslyEgocentric (m <*> (xB <*> xK <*> m))
    question4 bluebird m mock xK kestrel x = 
        let eq1 = sym $ cong (<*> x) $ question2b bluebird m mock xK
            eq2 = kestrel (m <*> ((xB <*> xK) <*> m)) x
        in trans eq1 eq2 

    question5 : {xB : b} -> Bluebird xB -> Dove
    question5 bluebird = 
        MkDove (xB <*> xB) 
            (\x => \y => \z => \w => 
                let eq1 = bluebird xB x y
                    eq2 = bluebird (x <*> y) z w
                in rewrite eq1 in eq2)
    --Dxyzw = BBxyzw = B(xy)zw = xy(zw)

    question6 : {xB : b} -> Bluebird xB -> Blackbird
    question6 bluebird = 
        let MkDove xD dove = question5 bluebird
        in MkBlackbird (xD <*> xB) 
            (\x => \y => \z => \w => 
                let eq1 = bluebird x (y <*> z) w
                    eq2 = dove xB x y z
                in trans (cong (<*> w) eq2) eq1)
    --x(yzw) = x((yz)w) = Bx(yz)w
    --Bx(yz) = DBxyz
    --B1 = DB

    question7 : {xB : b} -> Bluebird xB -> Eagle
    question7 bluebird = 
        let MkBlackbird xB1 blackbird = question6 bluebird
        in MkEagle (xB <*> xB1) 
            (\x => \y => \z => \w => \v =>
                let eq1 = blackbird (x <*> y) z w v
                    eq2 = bluebird xB1 x y
                in trans (cong (<*> v) $ cong (<*> w) $ cong (<*> z) eq2) eq1)
    --xy(zwv) = (xy)(zwv) = B1(xy)zwv 
    --B1(xy) = BB1xy
    --B1(xy)zwv = BB1xyzwv

    question8 : {xB : b} -> Bluebird xB -> Bunting
    question8 bluebird = 
        let MkEagle xE eagle = question7 bluebird
        in MkBunting (xE <*> xB) 
            (\x => \y => \z => \w => \v =>
                let eq1 = eagle xB x y z w
                    eq2 = bluebird x ((y <*> z) <*> w) v
                in trans (cong (<*> v) eq1) eq2)
    --x(yzwv) = x((yzw)v) = Bx(yzw)v
    --Bx(yzw) = EBxyzw
    --Bx(yzw)v = EBxyzwv

    question9 : {xB : b} -> Bluebird xB -> Dickcissel
    question9 bluebird = 
        let MkDove xD dove = question5 bluebird
        in MkDickcissel (xB <*> xD) 
            (\x => \y => \z => \w => \v =>
                let eq1 = bluebird xD x y
                    eq2 = dove (x <*> y) z w v
                    eq3 = cong (<*> z <*> w <*> v) eq1
                in trans eq3 eq2)
    --xyz(wv) = (xy)z(wv)
    --(xy)z(wv) = D(xy)zwv  eq2
    --D(xy) = BDxy          eq1
    --D(xy)zwv = BDxyzwv

    question9b : {xB : b} -> Bluebird xB -> Dickcissel
    question9b bluebird = 
        let MkBlackbird xB1 blackbird = question6 bluebird
        in MkDickcissel (xB1 <*> xB) 
            (\x => \y => \z => \w => \v =>
                let eq1 = bluebird (x <*> y <*> z) w v
                    eq2 = cong (<*> w <*> v) $ blackbird xB x y z
                in trans eq2 eq1)
    --xyz(wv) = (xyz)(wv) = B(xyz)wv    eq1
    --B(xyz) = B1Bxyz

    question10 : {xB : b} -> Bluebird xB -> Becard
    question10 bluebird = 
        let MkDickcissel xD1 dickcissel = question9 bluebird
        in MkBecard (xD1 <*> xB) 
            (\x => \y => \z => \w => 
                let eq1 = dickcissel xB x y z w
                    eq2 = bluebird x y (z <*> w)
                in trans eq1 eq2)
    --x(y(zw)) = Bxy(zw) = D1Bxyzw

    question11 : {xB : b} -> Bluebird xB -> Dovekie
    question11 bluebird = 
        let MkDove xD dove = question5 bluebird
        in MkDovekie (xD <*> xD) 
            (\x => \y => \z => \w => \v => 
                let eq1 = cong (<*> w <*> v) $ dove xD x y z
                    eq2 = dove x (y <*> z) w v
                in trans eq1 eq2)
    --x(yz)(wv) = Dx(yz)wv  eq2
    --Dx(yz) = DDxyz    eq1 

    question11b : {xB : b} -> Bluebird xB -> Dovekie
    question11b bluebird = 
        let MkBecard xB3 becard = question10 bluebird
        in MkDovekie (xB3 <*> xB) 
            (\x => \y => \z => \w => \v => 
                let eq1 = becard xB x y z
                    eq2 = bluebird (x <*> (y <*> z)) w v
                    eq3 = cong (<*> w <*> v) eq1
                in trans eq3 eq2)
    --x(yz)(wv) = B(x(yz))wv    eq2
    --B(x(yz)) = B3Bxyz eq1

    question12 : {xB : b} -> Bluebird xB -> BaldEagle
    question12 bluebird = 
        let MkEagle xE eagle = question7 bluebird
        in MkBaldEagle (xE <*> xE) 
            (\x => 
                \y1 => \y2 => \y3 => 
                \z1 => \z2 => \z3 => 
                    let eq1 = eagle x (y1 <*> y2 <*> y3) z1 z2 z3
                        eq2 = cong (<*> z1 <*> z2 <*> z3) $ eagle xE x y1 y2 y3
                    in trans eq2 eq1)
        --x(y1y2y3)(z1z2z3) = Ex(y1y2y3)z1z2z3
        --Ex(y1y2y3) = EExy1y2y3

    Warbler : b -> Type 
    Warbler xW = (x : b) -> (y : b) -> xW <*> x <*> y = x <*> y <*> y

    question14 : {xW : b} -> Warbler xW -> {xI : b} -> Identity xI -> (m ** Mockingbird m)
    question14 warbler ident = 
        (xW <*> xI ** \x => 
            let eq1 = warbler xI x
                eq2 = cong (<*> x) $ ident x
            in trans eq1 eq2)

    question15 : {xW : b} -> Warbler xW -> {xK : b} -> Kestrel xK -> (xI ** Identity xI)
    question15 warbler kestrel = 
        (xW <*> xK ** \x => 
            let eq1 = warbler xK x
                eq2 = kestrel x x
            in trans eq1 eq2)
    

    question13 : {xW : b} -> Warbler xW -> {xK : b} -> Kestrel xK -> (m ** Mockingbird m)
    question13 warbler kestrel = 
        let (xI ** ident) = question15 warbler kestrel
        in question14 warbler ident
    
    Cardinal : b -> Type
    Cardinal xC = (x : b) -> (y : b) -> (z : b) -> xC <*> x <*> y <*> z = x <*> z <*> y

    question16 : {xC : b} -> Cardinal xC -> {xK : b} -> Kestrel xK -> (xI ** Identity xI)
    question16 cardinal kestrel = 
        (xC <*> xK <*> xK ** \x => 
            let eq1 = cardinal xK xK x
                eq2 = kestrel x xK
            in trans eq1 eq2)
    
    Thrush : b -> Type
    Thrush xT = (x : b) -> (y : b) -> xT <*> x <*> y = y <*> x

    question17 : {xC : b} -> Cardinal xC -> {xI : b} -> Identity xI -> (xT ** Thrush xT)
    question17 cardinal ident = 
        (xC <*> xI ** \x => \y => 
            let eq1 = cardinal xI x y
                eq2 = cong (<*> x) $ ident y
            in trans eq1 eq2)

    question18 : {xT : b} -> Thrush xT -> ((x :b) -> (y ** Fond x y)) -> (xA ** ((x : b) -> xA <*> x = x <*> xA))
    question18 thrush prf = 
        let (xA**eq1) = prf xT
        in (xA ** \x => 
            let eq2 = cong (<*> x) eq1
                eq3 = thrush xA x
            in trans (sym eq2) eq3)
    --TA = A    eq1
    --TAx = Ax  eq2
    --TAx = xA  eq3

    question19 : {xB : b} -> Bluebird xB -> {xT : b} -> Thrush xT -> {m : b} -> Mockingbird m -> (xA ** ((x : b) -> xA <*> x = x <*> xA))
    question19 bluebird thrush mock =  
        question18 thrush (\x => 
            let prf = question2 bluebird m mock x
            in ((((xB <*> x) <*> m) <*> ((xB <*> x) <*> m)) ** prf))
    
    Robin : b -> Type 
    Robin xR = (x : b) -> (y : b) -> (z : b) -> xR <*> x <*> y <*> z = y <*> z <*> x

    question20 : {xB : b} -> Bluebird xB -> {xT : b} -> Thrush xT -> (xR ** Robin xR)
    question20 bluebird thrush = 
        let MkDove xD dove = question5 bluebird
        in (xD <*> xT ** \x => \y => \z => 
            let eq1 = dove xT x y z
                eq2 = thrush x (y <*> z)
            in trans eq1 eq2)
    
    question21' : {xR : b} -> Robin xR -> Cardinal (xR <*> xR <*> xR)
    question21' robin x y z = 
        let eq1 = cong (<*> y <*> z) $ robin xR xR x
            eq2 = cong (<*> z) $ robin x xR y
        in trans eq1 $ trans eq2 $ robin y x z

    question21 : {xR : b} -> Robin xR -> (xC ** Cardinal xC)
    question21 robin = 
        (xR <*> xR <*> xR ** 
            question21' robin)

    question22a : {xR : b} -> Robin xR -> {xC : b} -> Cardinal xC -> (x : b) -> (y : b) -> (z : b) -> xC <*> x <*> y <*> z = xR <*> x <*> xR <*> y <*> z 
    question22a robin cardinal x y z = 
        let eq1 = cong (<*> z) $ robin x xR y
            eq2 = robin y x z
            eq3 = cardinal x y z
        in sym $ trans eq1 $ trans eq2 $ sym eq3
    --Cx = RRRx = RxR

    question22b : 
        {xB : b} -> Bluebird xB -> 
        {xR : b} -> Robin xR ->
        {xT : b} -> Thrush xT ->  
        {xC : b} -> Cardinal xC -> 
        (x : b) -> (y : b) -> (z : b) ->
        xC <*> x <*> y <*> z = xB <*> (xT <*> x) <*> xR <*> y <*> z
    question22b bluebird robin thrush cardinal x y z = 
        let eq1 = cong (<*> z) $ bluebird (xT <*> x) xR y
            eq2 = cong (<*> z) $ thrush x (xR <*> y)
            eq3 = robin y x z
            eq4 = cardinal x y z
        in sym $ trans eq1 $ trans eq2 $ trans eq3 $ sym eq4

    question23 : {xC : b} -> Cardinal xC -> (xR ** Robin xR)
    question23 cardinal = 
        (xC <*> xC ** 
            \x => \y => \z => 
                let eq1 = cardinal xC x y
                    eq2 = cong (<*> z) eq1
                    eq3 = cardinal y x z
                in trans eq2 eq3)
        --CCxy = CYx        eq1
        --CCxyz = Cyxz = yzx
    
    Finch : b -> Type 
    Finch xF = (x : b) -> (y : b) -> (z : b) -> xF <*> x <*> y <*> z = z <*> y <*> x

    question24 : {xB : b} -> Bluebird xB -> {xR : b} -> Robin xR -> {xC : b} -> Cardinal xC -> (xF ** Finch xF)
    question24 bluebird robin cardinal = 
        (xB <*> xC <*> xR ** 
            \x => \y => \z => 
                let eq1 = robin x z y
                    eq2 = cardinal (xR <*> x) y z
                    eq3 = cong (<*> y <*> z) $ bluebird xC xR x
                in trans eq3 $ trans eq2 eq1)
    --zyx = Rxzy = (Rx)zy = C(Rx)yz = BCRxyz

    question25 : {xT : b} -> Thrush xT ->  Eagle -> (xF ** Finch xF)
    question25 thrush (MkEagle xE eagle) = 
        (xE <*> xT <*> xT <*> xE <*> xT ** 
            \x => \y => \z => 
                let eq1 = thrush x (z <*> y)
                    eq2 = cong ((xT <*> x) <*>) $ thrush y z
                    eq3 = eagle xT x xT y z
                    eq4 = cong (<*> y <*> z) $ thrush xT (xE <*> xT <*> x)
                    eq5 = cong (<*> y <*> z) $ eagle xT xT xE xT x
                in trans eq5 $ trans eq4 $ trans eq3 $ trans eq2 eq1)
    --zyx = Tx(zy) = Tx(Tyz) = ETxTyz = (ETx)Tyz = TT(ETx)yz 
    --(ETx)T = TT(ETx)      
    --TT(ETx) = ETTETx
    --TT(ETx)yz = ETTETxyz

    Vireo : b -> Type 
    Vireo xV = (x : b) -> (y : b) -> (z : b) -> xV <*> x <*> y <*> z = z <*> x <*> y

    question27 : {xB : b} -> Bluebird xB -> {xT : b} -> Thrush xT -> (xV ** Vireo xV)
    question27 bluebird thrush = 
        let (xF**finch) = question25 thrush $ question7 bluebird
            (xR**robin) = question20 bluebird thrush
            (xC**cardinal) = question21 robin
        in (xC <*> xF ** 
            \x => \y => \z => 
                let eq1 = cong (<*> z) $ cardinal xF x y
                    eq2 = finch y x z
                in trans eq1 eq2)
    --zxy = Fyxz = CFxyz

    question28 : {xF : b} -> Finch xF -> {xR : b} -> Robin xR -> (xV ** Vireo xV)
    question28 finch robin = 
        (xR <*> xF <*> xR ** 
            \x => \y => \z => 
                let eq1 = cong (<*> y <*> z) $ robin xF xR x
                    eq2 = cong (<*> z) $ robin x xF y
                    eq3 = finch y x z
                in trans eq1 $ trans eq2 eq3)
    
    question29 : {xC : b} -> Cardinal xC -> {xV : b} -> Vireo xV -> (xF ** Finch xF)
    question29 cardinal vireo = 
        (xC <*> xV ** 
            \x => \y => \z => 
                let eq1 = cong (<*> z) $ cardinal xV x y
                    eq2 = vireo y x z
                in trans eq1 eq2)
    --CVxyz = Vyxz = zyx

    question30 : {xR : b} -> Robin xR -> {xK : b} -> Kestrel xK -> (xI ** Identity xI)
    question30 robin kestrel = 
        (xR <*> xR <*> xK ** 
            \x => 
                let eq1 = robin xR xK x
                    eq2 = kestrel x xR
                in trans eq1 eq2)
    --RAKx = KxA = x

    CardinalOnceRemoved : b -> Type 
    CardinalOnceRemoved xCstar = (x : b) -> (y : b) -> (z : b) -> (w : b) -> xCstar <*> x <*> y <*> z <*> w = x <*> y <*> w <*> z

    question31 : {xB : b} -> Bluebird xB -> {xC : b} -> Cardinal xC -> (xCstar ** CardinalOnceRemoved xCstar)
    question31 bluebird cardinal = 
        (xB <*> xC ** 
            \x => \y => \z => \w => 
                let eq1 = cong (<*> z <*> w) $ bluebird xC x y
                    eq2 = cardinal (x <*> y) z w
                in trans eq1 eq2)
    --xywz = (xy)wz = C(xy)zw = BCxyzw
    
    RobinOnceRemoved : b -> Type 
    RobinOnceRemoved xRstar = (x : b) -> (y : b) -> (z : b) -> (w : b) -> xRstar <*> x <*> y <*> z <*> w = x <*> z <*> w <*> y

    question32 : {xB : b} -> Bluebird xB -> {xC : b} -> Cardinal xC -> (xRstar ** RobinOnceRemoved xRstar)
    question32 bluebird cardinal = 
        let (xCstar**cardinalOnceRemoved) = question31 bluebird cardinal
        in (xCstar <*> xCstar ** 
            \x => \y => \z => \w => 
                let eq1 = cong (<*> w ) $ cardinalOnceRemoved xCstar x y z
                    eq2 = cardinalOnceRemoved x z y w
                in trans eq1 eq2)
    --xzwy = C*xzyw = C*C*xyzw
    --C*xzy - C*C*xyz

    FinchOnceRemoved : b -> Type 
    FinchOnceRemoved xFstar = (x : b) -> (y : b) -> (z : b) -> (w : b) -> xFstar <*> x <*> y <*> z <*> w = x <*> w <*> z <*> y

    question33 : {xB : b} -> Bluebird xB -> {xC : b} -> Cardinal xC -> (xFstar ** FinchOnceRemoved xFstar)
    question33 bluebird cardinal = 
        let (xCstar**cardinalOnceRemoved) = question31 bluebird cardinal
            (xRstar**robinOnceRemoved) = question32 bluebird cardinal
        in (xB<*>xCstar<*>xRstar ** 
            \x => \y => \z => \w => 
                let eq1 = cong (<*> y <*> z <*> w) $ bluebird xCstar xRstar x
                    eq2 = cardinalOnceRemoved (xRstar <*> x) y z w
                    eq3 = robinOnceRemoved x y w z
                in trans eq1 $ trans eq2 eq3)
    
    VireoOnceRemoved : b -> Type 
    VireoOnceRemoved xVstar = (x : b) -> (y : b) -> (z : b) -> (w : b) -> xVstar <*> x <*> y <*> z <*> w = x <*> w <*> y <*> z

    question34 : {xB : b} -> Bluebird xB -> {xC : b} -> Cardinal xC -> (xVstar ** VireoOnceRemoved xVstar)
    question34 bluebird cardinal = 
        let (xCstar**cardinalOnceRemoved) = question31 bluebird cardinal
            (xFstar**finchOnceRemoved) = question33 bluebird cardinal
        in (xCstar<*>xFstar ** 
            \x => \y => \z => \w => 
                let eq1 = cong (<*> w) $ cardinalOnceRemoved xFstar x y z
                    eq2 = finchOnceRemoved x z y w
                in trans eq1 eq2)
    
    CardinalTwiceRemoved : b -> Type 
    CardinalTwiceRemoved xCdstar = (x : b) -> (y : b) -> (z1 : b) -> (z2 : b) -> (z3 : b) -> xCdstar <*> x <*> y <*> z1 <*> z2 <*> z3 = x <*> y <*> z1 <*> z3 <*> z2
    RobinTwiceRemoved : b -> Type 
    RobinTwiceRemoved xRdstar = (x : b) -> (y : b) -> (z1 : b) -> (z2 : b) -> (z3 : b) -> xRdstar <*> x <*> y <*> z1 <*> z2 <*> z3 = x <*> y <*> z2 <*> z3 <*> z1
    FinchTwiceRemoved : b -> Type 
    FinchTwiceRemoved xFdstar = (x : b) -> (y : b) -> (z1 : b) -> (z2 : b) -> (z3 : b) -> xFdstar <*> x <*> y <*> z1 <*> z2 <*> z3 = x <*> y <*> z3 <*> z2 <*> z1
    VireoTwiceRemoved : b -> Type 
    VireoTwiceRemoved xVdstar = (x : b) -> (y : b) -> (z1 : b) -> (z2 : b) -> (z3 : b) -> xVdstar <*> x <*> y <*>z1 <*> z2 <*> z3 = x <*> y <*> z3 <*> z1 <*> z2

    question35a : {xB : b} -> Bluebird xB -> {xC : b} -> Cardinal xC -> (xCdstar ** CardinalTwiceRemoved xCdstar)
    question35a bluebird cardinal = 
        let (xCstar**cardinalOnceRemoved) = question31 bluebird cardinal
        in (xB<*>xCstar ** 
            \x => \y => \z1 => \z2 => \z3 => 
                let eq1 = cong (<*> z1 <*> z2 <*> z3) $ bluebird xCstar x y
                    eq2 = cardinalOnceRemoved (x <*> y) z1 z2 z3
                in trans eq1 eq2)
    --BC*

    question35b : {xB : b} -> Bluebird xB -> {xC : b} -> Cardinal xC -> (xRdstar ** RobinTwiceRemoved xRdstar)
    question35b bluebird cardinal =     
        let (xRstar**robinOnceRemoved) = question32 bluebird cardinal
        in (xB<*>xRstar ** 
            \x => \y => \z1 => \z2 => \z3 => 
                let eq1 = cong (<*> z1 <*> z2 <*> z3) $ bluebird xRstar x y
                    eq2 = robinOnceRemoved (x <*> y) z1 z2 z3
                in trans eq1 eq2)
    --BR*

    question35c : {xB : b} -> Bluebird xB -> {xC : b} -> Cardinal xC -> (xFdstar ** FinchTwiceRemoved xFdstar)
    question35c bluebird cardinal =     
        let (xFstar**finchOnceRemoved) = question33 bluebird cardinal
        in (xB<*>xFstar ** 
            \x => \y => \z1 => \z2 => \z3 => 
                let eq1 = cong (<*> z1 <*> z2 <*> z3) $ bluebird xFstar x y
                    eq2 = finchOnceRemoved (x <*> y) z1 z2 z3
                in trans eq1 eq2)
    --BF*

    question35d : {xB : b} -> Bluebird xB -> {xC : b} -> Cardinal xC -> (xVdstar ** VireoTwiceRemoved xVdstar)
    question35d bluebird cardinal =     
        let (xVstar**vireoOnceRemoved) = question34 bluebird cardinal
        in (xB<*>xVstar ** 
            \x => \y => \z1 => \z2 => \z3 => 
                let eq1 = cong (<*> z1 <*> z2 <*> z3) $ bluebird xVstar x y
                    eq2 = vireoOnceRemoved (x <*> y) z1 z2 z3
                in trans eq1 eq2)
    --BV*

    question36 : {xCstar : b} -> CardinalOnceRemoved xCstar -> {xT : b} -> Thrush xT -> (xV ** Vireo xV)
    question36 cardinalOnceRemoved thrush = 
        (xCstar<*>xT ** 
            \x => \y => \z => 
                let eq1 = cardinalOnceRemoved xT x y z
                    eq2 = cong (<*> y) $ thrush x z
                in trans eq1 eq2)
    --C*Txyz = Txzy = zxy

    QueerBird : b -> Type
    QueerBird xQ = (x : b) -> (y : b) -> (z : b) -> xQ <*> x <*> y <*> z = y <*> (x <*> z)

    question37 : {xB : b} -> Bluebird xB -> {xC : b} -> Cardinal xC -> (xQ ** QueerBird xQ)
    question37 bluebird cardinal = 
        (xC <*> xB ** 
            \x => \y => \z =>   
                let eq1 = cong (<*> z) $ cardinal xB x y
                    eq2 = bluebird y x z
                in trans eq1 eq2)    
    --y(xz) = Byxz = CBxyz

    QuixoticBird : b -> Type 
    QuixoticBird xQ1 = (x : b) -> (y : b) -> (z : b) -> xQ1 <*> x <*> y <*> z = x <*> (z <*> y)

    question38 : {xB : b} -> Bluebird xB -> {xC : b} -> Cardinal xC -> (xQ1 ** QuixoticBird xQ1)
    question38 bluebird cardinal = 
        let (xCstar**cardinalOnceRemoved) = question31 bluebird cardinal
        in (xCstar<*>xB ** 
            \x => \y => \z =>   
                let eq1 = cardinalOnceRemoved xB x y z
                    eq2 = bluebird x z y
                in trans eq1 eq2)
    --x(zy) = Bxzy = C*Bxyz

    QuizzicalBird : b -> Type 
    QuizzicalBird xQ2 = (x : b) -> (y : b) -> (z : b) -> xQ2 <*> x <*> y <*> z = y <*> (z <*> x)

    question39 : {xB : b} -> Bluebird xB -> {xC : b} -> Cardinal xC -> (xQ2 ** QuizzicalBird xQ2)
    question39 bluebird cardinal = 
        let (xRstar**robinOnceRemoved) = question32 bluebird cardinal
        in (xRstar<*>xB ** 
            \x => \y => \z =>   
                let eq1 = robinOnceRemoved xB x y z
                    eq2 = bluebird y z x
                in trans eq1 eq2)
    
    question40a : {xC : b} -> Cardinal xC -> {xQ1 : b} -> QuixoticBird xQ1 ->  (xQ2 ** QuizzicalBird xQ2)
    question40a cardinal quixotic = 
        (xC<*>xQ1 ** 
            \x => \y => \z =>   
                let eq1 = cong (<*> z) $ cardinal xQ1 x y
                    eq2 = quixotic y x z
                in trans eq1 eq2)
    
    question40b : {xC : b} -> Cardinal xC -> {xQ2 : b} -> QuizzicalBird xQ2 ->  (xQ1 ** QuixoticBird xQ1)
    question40b cardinal quizzical = 
        (xC<*>xQ2 ** 
            \x => \y => \z =>   
                let eq1 = cong (<*> z) $ cardinal xQ2 x y
                    eq2 = quizzical y x z
                in trans eq1 eq2)

    QuirkyBird : b -> Type 
    QuirkyBird xQ3 = (x : b) -> (y : b) -> (z : b) -> xQ3 <*> x <*> y <*> z = z <*> (x <*> y)

    question41 : {xB : b} -> Bluebird xB -> {xT : b} -> Thrush xT -> (xQ3 ** QuirkyBird xQ3)
    question41 bluebird thrush = 
        (xB <*> xT ** 
            \x => \y => \z =>   
                let eq1 = cong (<*> z) $ bluebird xT x y
                    eq2 = thrush (x <*> y) z
                in trans eq1 eq2)
    
    QuackyBird : b -> Type 
    QuackyBird xQ4 = (x : b) -> (y : b) -> (z : b) -> xQ4 <*> x <*> y <*> z = z <*> (y <*> x)

    question42 : {xB : b} -> Bluebird xB -> {xC : b} -> Cardinal xC -> (xQ4 ** QuackyBird xQ4)
    question42 bluebird cardinal = 
        let (xFstar**finchOnceRemoved) = question33 bluebird cardinal
        in (xFstar<*>xB ** 
            \x => \y => \z =>   
                let eq1 = finchOnceRemoved xB x y z
                    eq2 = bluebird z y x
                in trans eq1 eq2)


    question43a : {xC : b} -> Cardinal xC -> {xQ3: b} -> QuirkyBird xQ3 ->  (xQ4 ** QuackyBird xQ4)
    question43a cardinal quirky = 
        (xC<*>xQ3 ** 
            \x => \y => \z =>   
                let eq1 = cong (<*> z) $ cardinal xQ3 x y
                    eq2 = quirky y x z
                in trans eq1 eq2)
    
    question43b : {xC : b} -> Cardinal xC -> {xQ4 : b} -> QuackyBird xQ4 ->  (xQ3 ** QuirkyBird xQ3)
    question43b cardinal quacky = 
        (xC<*>xQ4 ** 
            \x => \y => \z =>   
                let eq1 = cong (<*> z) $ cardinal xQ4 x y
                    eq2 = quacky y x z
                in trans eq1 eq2)

    question44 : {xT : b} -> Thrush xT -> {xQ1 : b} -> QuixoticBird xQ1 -> QuackyBird (xQ1 <*> xT)
    question44 thrush quixotic x y z = 
        let eq1 = cong (<*> z) $ quixotic xT x y
            eq2 = thrush (y <*> x) z
        in trans eq1 eq2

    question45 : {xT : b} -> Thrush xT -> {xQ : b} -> QueerBird xQ -> (xB ** Bluebird xB)
    question45 thrush queer = 
        (xQ <*> xT <*> (xQ <*> xQ) ** 
            \x => \y => \z =>   
                let eq1 = cong (<*> y <*> z) $ queer xT (xQ <*> xQ) x
                    eq2 = cong (<*> z) $ queer xQ (xT <*> x) y
                    eq3 = cong (<*> z) $ thrush x (xQ <*> y)
                    eq4 = queer y x z
                in trans eq1 $ trans eq2 $ trans eq3 eq4)
    
    question46 : {xT : b} -> Thrush xT -> {xQ : b} -> QueerBird xQ -> (xC ** Cardinal xC)
    question46 thrush queer = 
        (xQ <*> xQ <*> (xQ <*> xT) ** 
            \x => \y => \z =>  
                let eq1 = cong (<*> y <*> z) $ queer xQ (xQ <*> xT) x
                    eq2 = cong (<*> z) $ queer xT (xQ <*> x) y
                    eq3 = queer x (xT <*> y) z
                    eq4 = thrush y (x <*> z)
                in trans eq1 $ trans eq2 $ trans eq3 eq4)
    
    Goldfinch : b -> Type 
    Goldfinch xG = (x : b) -> (y : b) -> (z : b) -> (w : b) -> xG <*> x <*> y <*> z <*> w = x <*> w <*> (y <*> z)

    question47 : {xB : b} -> Bluebird xB -> {xC : b} -> Cardinal xC -> (xG ** Goldfinch xG)
    question47 bluebird cardinal = 
        (xB<*>xB<*>xC ** 
            \x => \y => \z => \w => 
                let eq1 = cong (<*> y <*> z <*> w) $ bluebird xB xC x
                    eq2 = cong (<*> w) $ bluebird (xC <*> x) y z
                    eq3 = cardinal x (y <*> z) w
                in trans eq1 $ trans eq2 eq3)
    