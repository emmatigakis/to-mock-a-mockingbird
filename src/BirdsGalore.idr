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
