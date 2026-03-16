module MockingbirdsWarblersAndStarlings

import ToMockAMockingbird
import BirdsGalore

parameters {auto b : Type} {auto _ : Bird b}
    public export
    DoubleMockingbird : b -> Type
    DoubleMockingbird xM2 = (x : b) -> (y : b) -> xM2 <*> x <*> y = x <*> y <*> (x <*> y)

    export
    question1 : {xB : b} -> Bluebird xB -> {m : b} -> Mockingbird m -> (xM2 ** DoubleMockingbird xM2)
    question1 bluebird mock = 
        (xB <*> m ** 
            \x => \y =>
                let eq1 = bluebird m x y
                    eq2 = mock (x <*> y)
                in trans eq1 eq2)
    
    export
    question2 : {xB : b} -> Bluebird xB -> {m : b} -> Mockingbird m -> {xT : b} -> Thrush xT -> (xL ** Lark xL)
    question2 bluebird mock thrush = 
        let (xR**robin) = BirdsGalore.question20 bluebird thrush
            (xC**cardinal) = BirdsGalore.question21 robin
        in (xC<*>xB<*>m ** 
            \x => \y =>
                let eq1 = cong (<*> y) $ cardinal xB m x
                    eq2 = bluebird x m y
                    eq3 = cong (x <*>) $ mock y
                in trans eq1 $ trans eq2 eq3)
    
    export
    question3 : {xB : b} -> Bluebird xB -> {xW : b} -> Warbler xW -> (xL ** Lark xL)
    question3 bluebird warbler = 
        (xB <*> xW <*> xB ** 
            \x => \y =>
                let eq1 = cong (<*> y) $ bluebird xW xB x
                    eq2 = warbler (xB <*> x) y
                    eq3 = bluebird x y y 
                in trans eq1 $ trans eq2 eq3)
    
    export
    question4 : {m : b} -> Mockingbird m -> {xQ : b} -> QueerBird xQ -> (xL ** Lark xL)
    question4 mock queer = 
        (xQ<*>m ** 
            \x => \y =>
                let eq1 = queer m x y
                    eq2 = cong (x<*>) $ mock y
                in trans eq1 eq2)
    

    public export
    ConverseWarbler : b -> Type 
    ConverseWarbler xW' = (x : b) -> (y : b) -> xW' <*> x <*> y = y <*> x <*> x

    export
    question5 : {xB : b} -> Bluebird xB -> {m : b} -> Mockingbird m -> {xT : b} -> Thrush xT -> (xW' ** ConverseWarbler xW')
    question5 bluebird mock thrush = 
        let (xR**robin) = BirdsGalore.question20 bluebird thrush
            (xM2**dmock) = question1 bluebird mock
        in (xM2<*>xR ** 
            \x => \y =>
                let eq1 = cong (<*> y) $ dmock xR x
                    --eq2 = cong (<*>y) $ sym $ mock (xR <*> x)
                    eq2 = robin x (xR <*> x) y
                    eq3 = robin x y x
                in trans eq1 $ trans eq2 eq3)
    --M2Rxy = Rx(Rx)y = Rxyx = yxx
    
    export
    question5' : {xB : b} -> Bluebird xB -> {m : b} -> Mockingbird m -> {xC : b} -> Cardinal xC -> (xW' ** ConverseWarbler xW')
    question5' bluebird mock cardinal = 
        let (xR**robin) = BirdsGalore.question23 cardinal
            (xM2**dmock) = question1 bluebird mock
        in (xM2<*>xR ** 
            \x => \y =>
                let eq1 = cong (<*> y) $ dmock xR x
                    --eq2 = cong (<*>y) $ sym $ mock (xR <*> x)
                    eq2 = robin x (xR <*> x) y
                    eq3 = robin x y x
                in trans eq1 $ trans eq2 eq3)

    export
    question6 : {xB : b} -> Bluebird xB -> {xR : b} -> Robin xR -> {xC : b} -> Cardinal xC -> {m : b} -> Mockingbird m -> (xW ** Warbler xW)
    question6 bluebird robin cardinal mock = 
        let (xW'**converseWarbler) = question5' bluebird mock cardinal
        in (xC<*>xW' ** 
            \x => \y =>
                let eq1 = cardinal xW' x y
                    eq2 = converseWarbler y x
                in trans eq1 eq2)
    
    export
    question7 : {xB : b} -> Bluebird xB -> {xT : b} -> Thrush xT -> {m : b} -> Mockingbird m -> (xW ** Warbler xW)
    question7 bluebird thrush mock = 
        let (xR**robin) = BirdsGalore.question20 bluebird thrush
            (xC**cardinal) = BirdsGalore.question21 robin
            (xW'**converseWarbler) = question5' bluebird mock cardinal
        in (xC<*>xW' ** 
            \x => \y =>
                let eq1 = cardinal xW' x y
                    eq2 = converseWarbler y x
                in trans eq1 eq2)

    export
    question8 : {xT : b} -> Thrush xT -> {xW : b} -> Warbler xW -> (m ** Mockingbird m)
    question8 thrush warbler = 
        (xW<*>xT ** 
            \x=> 
                let eq1 = warbler xT x
                    eq2 = thrush x x
                in trans eq1 eq2)
    
    public export
    WarblerStar : b -> Type 
    WarblerStar xWstar = (x : b) -> (y : b) -> (z : b) -> xWstar <*> x <*> y <*> z = x <*> y <*> z <*> z

    export
    question9a : {xB : b} -> Bluebird xB -> {xT : b} -> Thrush xT -> {m : b} -> Mockingbird m -> (xWstar ** WarblerStar xWstar)
    question9a bluebird thrush mock = 
        let (xW**warbler) = question7 bluebird thrush mock
        in (xB<*>xW ** 
            \x => \y => \z =>
                let eq1 = cong (<*> z) $ bluebird xW x y
                    eq2 = warbler (x <*> y) z
                in trans eq1 eq2)
    
    %ambiguity_depth 8
    public export
    WarblerDStar : b -> Type 
    WarblerDStar xWdstar = (x : b) -> (y : b) -> (z : b) -> (w : b) -> xWdstar <*> x <*> y <*> z <*> w = x <*> y <*> z <*> w <*> w

    export
    question9b : {xB : b} -> Bluebird xB -> {xT : b} -> Thrush xT -> {m : b} -> Mockingbird m -> (xWdstar ** WarblerDStar xWdstar)
    question9b bluebird thrush mock = 
        let (xWstar**warblerStar) = question9a bluebird thrush mock
        in (xB<*>xWstar ** 
            \x => \y => \z => \w =>
                let eq1 = cong (<*> z <*> w) $ bluebird xWstar x y
                    eq2 = warblerStar (x <*> y) z w
                in trans eq1 eq2)
    
    public export
    Hummingbird : b -> Type 
    Hummingbird xH = (x : b) -> (y : b) -> (z : b) -> xH <*> x <*> y <*> z = x <*> y <*> z <*> y

    export
    question10 : {xB : b} -> Bluebird xB -> {xT : b} -> Thrush xT -> {m : b} -> Mockingbird m -> (xH ** Hummingbird xH)
    question10 bluebird thrush mock = 
        let (xR**robin) = BirdsGalore.question20 bluebird thrush
            (xC**cardinal) = BirdsGalore.question21 robin
            (xCstar ** cardinalOnceRemoved) = question31 bluebird cardinal
            (xWstar**warblerStar) = question9a bluebird thrush mock
        in (xWstar<*>xCstar ** 
            \x => \y => \z =>
                let eq1 = cong (<*> z) $ warblerStar xCstar x y
                    eq2 = cardinalOnceRemoved x y y z
                in trans eq1 eq2)
    
    export
    question11 : {xC : b} -> Cardinal xC -> {xH : b} -> Hummingbird xH -> (xW ** Warbler xW)
    question11 cardinal hummingbird = 
        let (xR**robin) = BirdsGalore.question23 cardinal
        in (xC<*>(xH<*>xR) ** 
            \x => \y => 
                let eq1 = cardinal (xH <*> xR) x y
                    eq2 = hummingbird xR y x
                    eq3 = robin y x y 
                in trans eq1 $ trans eq2 eq3)
    
    public export
    Starling : b -> Type 
    Starling xS = (x : b) -> (y : b) -> (z : b) -> xS <*> x <*> y <*> z = x <*> z <*> (y <*> z)

    export
    question12 : {xB : b} -> Bluebird xB -> {xT : b} -> Thrush xT -> {m : b} -> Mockingbird m -> (xS ** Starling xS)
    question12 bluebird thrush mock = 
        let (xWdstar**warblerDStar) = question9b bluebird thrush mock
            (xR**robin) = BirdsGalore.question20 bluebird thrush
            (xC**cardinal) = BirdsGalore.question21 robin
            (xG**goldfinch) = BirdsGalore.question47 bluebird cardinal
        in (xWdstar<*>xG ** 
            \x => \y => \z =>
                let eq1 = warblerDStar xG x y z
                    eq2 = goldfinch x y z z
                in trans eq1 eq2)
    
    export
    question13 : {xS : b} -> Starling xS -> {xC : b} -> Cardinal xC -> (xH ** Hummingbird xH)
    question13 starling cardinal = 
        let (xR**robin) = BirdsGalore.question23 cardinal
        in (xS<*>xR ** 
            \x => \y => \z =>
                let eq1 = cong (<*> z) $ starling xR x y
                    eq2 = robin y (x <*> y) z
                in trans eq1 eq2)
    
    export
    question14a : {xS : b} -> Starling xS -> {xC : b} -> Cardinal xC -> (xW ** Warbler xW)
    question14a starling cardinal = 
        let (xH ** hummingbird) = question13 starling cardinal
        in question11 cardinal hummingbird

    export
    question14b : {xS : b} -> Starling xS -> {xR : b} -> Robin xR -> (xW ** Warbler xW)
    question14b starling robin = 
        let (xC**cardinal) = BirdsGalore.question21 robin
        in question14a starling cardinal
    
    export
    question15 : {xS : b} -> Starling xS -> {xT : b} -> Thrush xT -> (xW ** Warbler xW)
    question15 starling thrush = 
        (xS<*>xT ** 
            \x => \y =>
                let eq1 = starling xT x y
                    eq2 = thrush y (x <*> y) 
                in trans eq1 eq2)
    
    export
    question16 : {xS : b} -> Starling xS -> {xT : b} -> Thrush xT -> (m ** Mockingbird m)
    question16 starling thrush = 
        let (xW**warbler) = question15 starling thrush
        in question8 thrush warbler
    