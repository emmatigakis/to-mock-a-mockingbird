module BirdsGalore

import ToMockAMockingbird

%default total 

%ambiguity_depth 5
data Dove : {b : _} -> Bird b => Type where 
    MkDove : {b : _} -> Bird b => (xD : b) -> ((x : b) -> (y : b) -> (z : b) -> (w : b) -> xD <*> x <*> y <*> z <*> w = x <*> y <*> (z <*> w)) -> Dove {b=b}

data Blackbird : {b : _} -> Bird b => Type where
    MkBlackbird : {b : _} -> Bird b => (xB1 :b) -> ((x :b ) -> (y : b) -> (z : b) -> (w : b) -> xB1 <*> x <*> y <*> z <*> w = x <*> (y <*> z <*> w)) -> Blackbird {b=b}

data Eagle : {b : _} -> Bird b => Type where
    MkEagle : {b : _} -> Bird b => (xE : b) -> ((x :b ) -> (y : b) -> (z : b) -> (w : b) -> (v : b) -> xE <*> x <*> y <*> z <*> w <*> v = x <*> y <*> (z <*> w <*> v)) -> Eagle {b=b}

data Bunting : {b : _} -> Bird b => Type where
    MkBunting : {b : _} -> Bird b => (xB2 : b) -> ((x :b ) -> (y : b) -> (z : b) -> (w : b) -> (v : b) -> xB2 <*> x <*> y <*> z <*> w <*> v = x <*> (y <*> z <*> w <*> v)) -> Bunting {b=b}

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

    question5 : {xB : b} -> Bluebird xB -> Dove {b=b}
    question5 bluebird = 
        MkDove (xB <*> xB) 
            (\x => \y => \z => \w => 
                let eq1 = bluebird xB x y
                    eq2 = bluebird (x <*> y) z w
                in rewrite eq1 in eq2)
    -- question5 : {xB : b} -> Bluebird xB -> Dove (xB <*> xB)
    -- question5 bluebird x y z w = 
    --     let eq1 = bluebird xB x y
    --         eq2 = bluebird (x <*> y) z w
    --     in rewrite eq1 in eq2
    --Dxyzw = BBxyzw = B(xy)zw = xy(zw)

    question6 : {xB : b} -> Bluebird xB -> Blackbird {b=b}
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

    question7 : {xB : b} -> Bluebird xB -> Eagle {b=b}
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

    question8 : {xB : b} -> Bluebird xB -> Bunting {b=b}
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