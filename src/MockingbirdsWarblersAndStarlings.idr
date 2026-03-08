module MockingbirdsWarblersAndStarlings

import ToMockAMockingbird
import BirdsGalore

parameters {auto b : Type} {auto _ : Bird b}
    DoubleMockingbird : b -> Type
    DoubleMockingbird xM2 = (x : b) -> (y : b) -> xM2 <*> x <*> y = x <*> y <*> (x <*> y)

    question1 : {xB : b} -> Bluebird xB -> {m : b} -> Mockingbird m -> (xM2 ** DoubleMockingbird xM2)
    question1 bluebird mock = 
        (xB <*> m ** 
            \x => \y =>
                let eq1 = bluebird m x y
                    eq2 = mock (x <*> y)
                in trans eq1 eq2)
    
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
    
    question3 : {xB : b} -> Bluebird xB -> {xW : b} -> Warbler xW -> (xL ** Lark xL)
    question3 bluebird warbler = 
        (xB <*> xW <*> xB ** 
            \x => \y =>
                let eq1 = cong (<*> y) $ bluebird xW xB x
                    eq2 = warbler (xB <*> x) y
                    eq3 = bluebird x y y 
                in trans eq1 $ trans eq2 eq3)
    
    question4 : {m : b} -> Mockingbird m -> {xQ : b} -> QueerBird xQ -> (xL ** Lark xL)
    question4 mock queer = 
        (xQ<*>m ** 
            \x => \y =>
                let eq1 = queer m x y
                    eq2 = cong (x<*>) $ mock y
                in trans eq1 eq2)
    

    ConverseWarbler : b -> Type 
    ConverseWarbler xW' = (x : b) -> (y : b) -> xW' <*> x <*> y = y <*> x <*> x

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


    question6 : {xB : b} -> Bluebird xB -> {xR : b} -> Robin xR -> {xC : b} -> Cardinal xC -> {m : b} -> Mockingbird m -> (xW ** Warbler xW)
    question6 bluebird robin cardinal mock = 
        let (xW'**converseWarbler) = question5' bluebird mock cardinal
        in (xC<*>xW' ** 
            \x => \y =>
                let eq1 = cardinal xW' x y
                    eq2 = converseWarbler y x
                in trans eq1 eq2)
    
    question6' : {xB : b} -> Bluebird xB -> {xR : b} -> Robin xR -> {xT : b} -> Thrush xT -> {m : b} -> Mockingbird m -> (xW ** Warbler xW)
    question6' bluebird robin thrush mock = 
        let (xR**robin) = BirdsGalore.question20 bluebird thrush
            (xC**cardinal) = BirdsGalore.question21 robin
            (xW'**converseWarbler) = question5' bluebird mock cardinal
        in (xC<*>xW' ** 
            \x => \y =>
                let eq1 = cardinal xW' x y
                    eq2 = converseWarbler y x
                in trans eq1 eq2)
