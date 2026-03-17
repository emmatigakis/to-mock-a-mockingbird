module AGalleryOfSageBirds

import ToMockAMockingbird
import BirdsGalore
import MockingbirdsWarblersAndStarlings

%default total 


parameters {auto b : Type} {auto _ : Bird b}
    SageBird : b -> Type 
    SageBird theta = (x : b) -> theta <*> x = x <*> (theta <*> x)

    question1 : {m : b} -> Mockingbird m -> {xB : b} -> Bluebird xB -> {xR : b} -> Robin xR -> (theta ** SageBird theta)
    question1 mock bluebird robin = 
        (xB<*>m<*>(xR<*>m<*>xB) ** 
            \x =>
                let eq1 = bluebird m ((xR <*> m) <*> xB) x
                    eq2 = mock (((xR <*> m) <*> xB) <*> x)
                    eq3 = cong2 (<*>) (robin m xB x) (robin m xB x)
                    eq4 = sym $ BirdsGalore.question2 bluebird m mock x
                    eq5 = cong (x <*>) $ sym $ mock ((xB <*> x) <*> m)
                    eq6 = cong(x <*>) eq1
                    eq7 = cong (x <*>) $ cong (m<*>) $ robin m xB x
                    in trans eq1 $ trans eq2 $ trans eq3 $ trans eq4 $ trans eq5 $ sym $ trans eq6 eq7)
    
    question2 : {m : b} -> Mockingbird m -> {xB : b} -> Bluebird xB -> {xC : b} -> Cardinal xC -> (theta ** SageBird theta)
    question2 mock bluebird cardinal = 
        (xB<*>m<*>(xC<*>xB<*>m) ** 
            \x => 
                let eq1 = bluebird m ((xC <*> xB) <*> m) x
                    eq2 = mock (((xC <*> xB) <*> m) <*> x)
                    eq3 = cong2 (<*>) (cardinal xB m x) (cardinal xB m x)
                    eq4 = sym $ BirdsGalore.question2 bluebird m mock x
                    eq5 = cong (x <*>) $ sym $ mock ((xB <*> x) <*> m)
                    eq6 = cong(x <*>) eq1
                    eq7 = cong (x <*>) $ cong (m<*>) $ cardinal xB m x
                in trans eq1 $ trans eq2 $ trans eq3 $ trans eq4 $ trans eq5 $ sym $ trans eq6 eq7)
    
    question3 : {m : b} -> Mockingbird m -> {xB : b} -> Bluebird xB -> {xL : b} -> Lark xL -> (theta ** SageBird theta)
    question3 mock bluebird lark = 
        (xB<*>m<*>xL ** 
            \x => 
                let eq1 = bluebird m xL x
                    eq2 = mock (xL <*> x)
                    eq3 = sym $ lark_lemma lark x
                    eq4 = cong(x <*>) eq1
                    eq5 = cong (x <*>) $ mock (xL <*> x)
                in trans eq1 $ trans eq2 $ trans eq3 $ sym $ trans eq4 eq5)

    question4 : {m : b} -> Mockingbird m -> {xB : b} -> Bluebird xB -> {xW : b} -> Warbler xW -> (theta ** SageBird theta)
    question4 mock bluebird warbler = 
        let (xL**lark) = MockingbirdsWarblersAndStarlings.question3 bluebird warbler
        in question3 mock bluebird lark
    
    question6 : {xQ : b} -> QueerBird xQ -> {xL : b} -> Lark xL -> {xW : b} -> Warbler xW -> (theta ** SageBird theta)
    question6 queer lark warbler = 
        (xW<*>(xQ<*>xL<*>(xQ<*>xL)) ** 
            \x => 
                let eq1 = warbler ((xQ <*> xL) <*> (xQ <*> xL)) x
                    eq2 = cong (<*> x) $ queer xL (xQ <*> xL) x
                    eq3 = queer xL (xL <*> x) x
                    eq4 = lark x (xL <*> x)
                    eq5 = cong(x <*>) eq1
                    eq6 = cong(x <*>) eq2
                    eq7 = cong(x <*>) eq3
                in trans eq1 $ trans eq2 $ trans eq3 $ trans eq4 $ sym $ trans eq5 $ trans eq6 eq7)
    

    question5 : {xB : b} -> Bluebird xB -> {xW : b} -> Warbler xW -> {xC : b} -> Cardinal xC -> (theta ** SageBird theta)
    question5 bluebird warbler cardinal = 
        let (xL**lark) = MockingbirdsWarblersAndStarlings.question3 bluebird warbler
            (xQ**queer) = BirdsGalore.question37 bluebird cardinal
        in question6 queer lark warbler
    
    question8 : {xQ : b} -> QueerBird xQ -> {m : b} -> Mockingbird m -> (theta ** SageBird theta)
    question8 queer mock = 
        let (xL**lark) = MockingbirdsWarblersAndStarlings.question4 mock queer
        in question8' queer lark mock
    where 
        question8' : {xQ' : b} -> QueerBird xQ' -> {xL' : b} -> Lark xL' -> {m' : b} -> Mockingbird m' -> (theta ** SageBird theta)
        question8' queer lark mock = 
            (xQ'<*>xL'<*>m' ** 
                \x => 
                    let eq1 = queer xL' m' x
                        eq2 = mock (xL' <*> x)
                        eq3 = sym $ lark_lemma lark x
                        eq4 = cong(x <*>) eq1
                        eq5 = cong(x <*>) eq2
                    in trans eq1 $ trans eq2 $ trans eq3 $ sym $ trans eq4 eq5)

    question9 : {xS : b} -> Starling xS -> {xL : b} -> Lark xL -> (theta ** SageBird theta)
    question9 starling lark = 
        (xS<*>xL<*>xL ** 
            \x => 
                let eq1 = starling xL xL x
                    eq2 = sym $ lark_lemma lark x
                    eq3 = cong(x <*>) eq1
                in trans eq1 $ trans eq2 $ sym eq3)
    
    question10 : {xB : b} -> Bluebird xB -> {xW : b} -> Warbler xW -> {xS : b} -> Starling xS -> (theta ** SageBird theta)
    question10 bluebird warbler starling = 
        (xW<*>xS<*>(xB<*>xW<*>xB) ** 
            \x =>
                let eq1 = cong (<*> x) $ warbler xS ((xB <*> xW) <*> xB)
                    eq2 = starling ((xB <*> xW) <*> xB)  ((xB <*> xW) <*> xB) x
                    eq3 = cong2 (<*>) (bluebird xW xB x) (bluebird xW xB x)
                    eq4 = warbler (xB <*> x) (xW <*> (xB <*> x))
                    eq5 = bluebird x (xW <*> (xB <*> x)) (xW <*> (xB <*> x))
                    eq6 = cong (x<*>) eq1
                    eq7 = cong (x<*>) eq2
                    eq8 = cong (x<*>) eq3
                in trans eq1 $ trans eq2 $ trans eq3 $ trans eq4 $ trans eq5 
                    $ sym $ trans eq6 $ trans eq7 eq8)
    
    TuringBird : b -> Type 
    TuringBird xU = (x : b) -> (y : b) -> xU <*> x <*> y = y <*> (x <*> x <*> y)

    question11 : {m : b} -> Mockingbird m -> {xB : b} -> Bluebird xB -> {xT : b} -> Thrush xT -> (xU ** TuringBird xU)
    question11 mock bluebird thrush = 
        let (xL**lark) = MockingbirdsWarblersAndStarlings.question2 bluebird mock thrush
            (xW**warbler) = MockingbirdsWarblersAndStarlings.question7 bluebird thrush mock
            (xR**robin) = BirdsGalore.question20 bluebird thrush
            (xC**cardinal) = BirdsGalore.question21 robin
            (xQ**queer) = BirdsGalore.question37 bluebird cardinal
        in (xB<*>xW<*>(xL<*>xQ) ** 
            \x => \y => 
                let eq1 = cong (<*> y) $ bluebird xW (xL <*> xQ) x
                    eq2 = warbler ((xL <*> xQ) <*> x) y
                    eq3 = cong (<*> y <*> y) $ lark xQ x
                    eq4 = queer (x <*> x) y y
                in trans eq1 $ trans eq2 $ trans eq3 eq4)
    
    question12 : {xU : b} -> TuringBird xU -> (theta ** SageBird theta)
    question12 turing = 
        (xU<*>xU ** turing xU)
    
    Owl : b -> Type 
    Owl xO = (x : b) -> (y : b) -> xO <*> x <*> y = y <*> (x <*> y)

    question13 : {xB : b} -> Bluebird xB -> {xW : b} -> Warbler xW -> {xC : b} -> Cardinal xC -> (xO ** Owl xO)
    question13 bluebird warbler cardinal = 
        (xB<*>xW<*>(xC<*>xB) ** 
            \x => \y => 
                let eq1 = cong (<*> y) $ bluebird xW (xC <*> xB) x
                    eq2 = warbler ((xC <*> xB) <*> x) y
                    eq3 = cong (<*> y) $ cardinal xB x y
                    eq4 = bluebird y x y
                in trans eq1 $ trans eq2 $ trans eq3 eq4)
    
    question14 : {xO : b} -> Owl xO -> {xL : b} -> Lark xL -> (xU ** TuringBird xU)
    question14 owl lark = 
        (xL<*>xO ** 
            \x => \y => 
                let eq1 = cong (<*> y) $ lark xO x
                    eq2 = owl 
                    eq2 = owl (x <*> x) y
                in trans eq1 eq2)
    
    question15 : {xO : b} -> Owl xO -> {xI : b} -> Identity xI -> (m ** Mockingbird m)
    question15 owl ident = 
        (xO<*>xI ** 
            \x => 
                let eq1 = owl xI x
                    eq2 = cong (x<*>) $ ident x
                in trans eq1 eq2)

    question16 : {xS : b} -> Starling xS -> {xI : b} -> Identity xI -> (xO ** Owl xO)
    question16 starling ident = 
        (xS<*>xI ** 
            \x => \y => 
                let eq1 = starling xI x y
                    eq2 = cong (<*> (x <*> y)) $ ident y
                in trans eq1 eq2)
    
    question17 : Fond x y -> Fond x (x <*> y)
    question17 eq1 = 
        cong (x <*>) eq1
    
    question18 : {xO : b} -> Owl xO -> {theta : b} -> SageBird theta -> SageBird $ xO<*>theta
    question18 owl sage x = 
        let eq1 = owl theta x
            eq2 = cong (x<*>) eq1
            eq3 = cong (x <*>) $ sym $ sage x
        in trans eq1 $ sym $ trans eq2 eq3
    
    question19 : {xO : b} -> Owl xO -> {theta : b} -> SageBird theta -> SageBird $ theta<*>xO
    question19 owl sage x = 
        let eq1 = cong (<*> x) $ sage xO
            eq2 = owl (theta <*> xO) x
        in trans eq1 eq2
    
    question20 : {xO : b} -> Owl xO -> {xA : b} -> Fond xO xA -> SageBird xA
    question20 owl eq1 x = 
        let eq2 = sym $ cong (<*> x) eq1
            eq3 = owl xA x
        in trans eq2 eq3
    
    ChoosyBird : b -> Type 
    ChoosyBird xA = (xB : b) -> Fond xA xB -> SageBird xB

    question21 : {xA : b} -> ChoosyBird xA -> {theta : b} -> SageBird theta -> SageBird $ theta<*>xA
    question21 choosy sage x = 
        let eq1 = cong (<*> x) $ sage xA
            eq2 = (choosy (theta <*> xA) $ sym $ sage xA) x
        in trans eq1 $ trans (sym eq1) eq2
    
    