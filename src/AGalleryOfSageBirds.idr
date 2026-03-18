module AGalleryOfSageBirds

import Data.DPair
import ToMockAMockingbird
import BirdsGalore
import MockingbirdsWarblersAndStarlings

%default total 


parameters {auto b : Type} {auto _ : Bird b}
    0 SageBird : b -> Type 
    SageBird theta = (x : b) -> theta <*> x = x <*> (theta <*> x)

    0 question1 : {m : b} -> Mockingbird m -> {xB : b} -> Bluebird xB -> {xR : b} -> Robin xR -> Exists(\theta => SageBird theta)
    question1 mock bluebird robin = 
        Evidence (xB<*>m<*>(xR<*>m<*>xB)) $
            \x =>
                let eq1 = bluebird m ((xR <*> m) <*> xB) x
                    eq2 = mock (((xR <*> m) <*> xB) <*> x)
                    eq3 = cong2 (<*>) (robin m xB x) (robin m xB x)
                    eq4 = sym $ BirdsGalore.question2 bluebird m mock x
                    eq5 = cong (x <*>) $ sym $ mock ((xB <*> x) <*> m)
                    eq6 = cong(x <*>) eq1
                    eq7 = cong (x <*>) $ cong (m<*>) $ robin m xB x
                    in trans eq1 $ trans eq2 $ trans eq3 $ trans eq4 $ trans eq5 $ sym $ trans eq6 eq7
    
    0 question2 : {m : b} -> Mockingbird m -> {xB : b} -> Bluebird xB -> {xC : b} -> Cardinal xC -> Exists(\theta => SageBird theta)
    question2 mock bluebird cardinal = 
        Evidence (xB<*>m<*>(xC<*>xB<*>m)) $
            \x => 
                let eq1 = bluebird m ((xC <*> xB) <*> m) x
                    eq2 = mock (((xC <*> xB) <*> m) <*> x)
                    eq3 = cong2 (<*>) (cardinal xB m x) (cardinal xB m x)
                    eq4 = sym $ BirdsGalore.question2 bluebird m mock x
                    eq5 = cong (x <*>) $ sym $ mock ((xB <*> x) <*> m)
                    eq6 = cong(x <*>) eq1
                    eq7 = cong (x <*>) $ cong (m<*>) $ cardinal xB m x
                in trans eq1 $ trans eq2 $ trans eq3 $ trans eq4 $ trans eq5 $ sym $ trans eq6 eq7
    
    0 question3 : {m : b} -> Mockingbird m -> {xB : b} -> Bluebird xB -> {xL : b} -> Lark xL -> Exists(\theta => SageBird theta)
    question3 mock bluebird lark = 
        Evidence (xB<*>m<*>xL) $
            \x => 
                let eq1 = bluebird m xL x
                    eq2 = mock (xL <*> x)
                    eq3 = sym $ lark_lemma lark x
                    eq4 = cong(x <*>) eq1
                    eq5 = cong (x <*>) $ mock (xL <*> x)
                in trans eq1 $ trans eq2 $ trans eq3 $ sym $ trans eq4 eq5

    0 question4 : {m : b} -> Mockingbird m -> {xB : b} -> Bluebird xB -> {xW : b} -> Warbler xW -> Exists(\theta => SageBird theta)
    question4 mock bluebird warbler = 
        let Evidence xL lark = MockingbirdsWarblersAndStarlings.question3 bluebird warbler
        in question3 mock bluebird lark
    
    question6 : {xQ : b} -> QueerBird xQ -> {xL : b} -> Lark xL -> {xW : b} -> Warbler xW -> Exists(\theta => SageBird theta)
    question6 queer lark warbler = 
        Evidence (xW<*>(xQ<*>xL<*>(xQ<*>xL))) $
            \x => 
                let eq1 = warbler ((xQ <*> xL) <*> (xQ <*> xL)) x
                    eq2 = cong (<*> x) $ queer xL (xQ <*> xL) x
                    eq3 = queer xL (xL <*> x) x
                    eq4 = lark x (xL <*> x)
                    eq5 = cong(x <*>) eq1
                    eq6 = cong(x <*>) eq2
                    eq7 = cong(x <*>) eq3
                in trans eq1 $ trans eq2 $ trans eq3 $ trans eq4 $ sym $ trans eq5 $ trans eq6 eq7
    

    0 question5 : {xB : b} -> Bluebird xB -> {xW : b} -> Warbler xW -> {xC : b} -> Cardinal xC -> Exists(\theta => SageBird theta)
    question5 bluebird warbler cardinal = 
        let Evidence xL lark = MockingbirdsWarblersAndStarlings.question3 bluebird warbler
            Evidence xQ queer = BirdsGalore.question37 bluebird cardinal
        in question6 queer lark warbler
    
    0 question8 : {xQ : b} -> QueerBird xQ -> {m : b} -> Mockingbird m -> Exists(\theta => SageBird theta)
    question8 queer mock = 
        let Evidence xL lark = MockingbirdsWarblersAndStarlings.question4 mock queer
        in question8' queer lark mock
    where 
        question8' : {xQ' : b} -> QueerBird xQ' -> {xL' : b} -> Lark xL' -> {m' : b} -> Mockingbird m' -> Exists(\theta => SageBird theta)
        question8' queer lark mock = 
            Evidence (xQ'<*>xL'<*>m') $
                \x => 
                    let eq1 = queer xL' m' x
                        eq2 = mock (xL' <*> x)
                        eq3 = sym $ lark_lemma lark x
                        eq4 = cong(x <*>) eq1
                        eq5 = cong(x <*>) eq2
                    in trans eq1 $ trans eq2 $ trans eq3 $ sym $ trans eq4 eq5

    0 question9 : {xS : b} -> Starling xS -> {xL : b} -> Lark xL -> Exists(\theta => SageBird theta)
    question9 starling lark = 
        Evidence (xS<*>xL<*>xL) $
            \x => 
                let eq1 = starling xL xL x
                    eq2 = sym $ lark_lemma lark x
                    eq3 = cong(x <*>) eq1
                in trans eq1 $ trans eq2 $ sym eq3
    
    0 question10 : {xB : b} -> Bluebird xB -> {xW : b} -> Warbler xW -> {xS : b} -> Starling xS -> Exists(\theta => SageBird theta)
    question10 bluebird warbler starling = 
        Evidence (xW<*>xS<*>(xB<*>xW<*>xB)) $
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
                    $ sym $ trans eq6 $ trans eq7 eq8
    
    0 TuringBird : b -> Type 
    TuringBird xU = (x : b) -> (y : b) -> xU <*> x <*> y = y <*> (x <*> x <*> y)

    0 question11 : {m : b} -> Mockingbird m -> {xB : b} -> Bluebird xB -> {xT : b} -> Thrush xT -> Exists(\xU => TuringBird xU)
    question11 mock bluebird thrush = 
        let Evidence xL lark = MockingbirdsWarblersAndStarlings.question2 bluebird mock thrush
            Evidence xW warbler = MockingbirdsWarblersAndStarlings.question7 bluebird thrush mock
            Evidence xR robin = BirdsGalore.question20 bluebird thrush
            Evidence xC cardinal = BirdsGalore.question21 robin
            Evidence xQ queer = BirdsGalore.question37 bluebird cardinal
        in Evidence (xB<*>xW<*>(xL<*>xQ)) $
            \x => \y => 
                let eq1 = cong (<*> y) $ bluebird xW (xL <*> xQ) x
                    eq2 = warbler ((xL <*> xQ) <*> x) y
                    eq3 = cong (<*> y <*> y) $ lark xQ x
                    eq4 = queer (x <*> x) y y
                in trans eq1 $ trans eq2 $ trans eq3 eq4
    
    0 question12 : {xU : b} -> TuringBird xU -> Exists(\theta => SageBird theta)
    question12 turing = 
        Evidence (xU<*>xU) $ turing xU
    
    0 Owl : b -> Type 
    Owl xO = (x : b) -> (y : b) -> xO <*> x <*> y = y <*> (x <*> y)

    0 question13 : {xB : b} -> Bluebird xB -> {xW : b} -> Warbler xW -> {xC : b} -> Cardinal xC -> Exists(\xO => Owl xO)
    question13 bluebird warbler cardinal = 
        Evidence (xB<*>xW<*>(xC<*>xB)) $
            \x => \y => 
                let eq1 = cong (<*> y) $ bluebird xW (xC <*> xB) x
                    eq2 = warbler ((xC <*> xB) <*> x) y
                    eq3 = cong (<*> y) $ cardinal xB x y
                    eq4 = bluebird y x y
                in trans eq1 $ trans eq2 $ trans eq3 eq4
    
    0 question14 : {xO : b} -> Owl xO -> {xL : b} -> Lark xL -> Exists(\xU => TuringBird xU)
    question14 owl lark = 
        Evidence (xL<*>xO) $
            \x => \y => 
                let eq1 = cong (<*> y) $ lark xO x
                    eq2 = owl 
                    eq2 = owl (x <*> x) y
                in trans eq1 eq2
    
    0 question15 : {xO : b} -> Owl xO -> {xI : b} -> Identity xI -> Exists(\m => Mockingbird m)
    question15 owl ident = 
        Evidence (xO<*>xI) $
            \x => 
                let eq1 = owl xI x
                    eq2 = cong (x<*>) $ ident x
                in trans eq1 eq2

    0 question16 : {xS : b} -> Starling xS -> {xI : b} -> Identity xI -> Exists(\xO => Owl xO)
    question16 starling ident = 
        Evidence (xS<*>xI) $
            \x => \y => 
                let eq1 = starling xI x y
                    eq2 = cong (<*> (x <*> y)) $ ident y
                in trans eq1 eq2
    
    0 question17 : Fond x y -> Fond x (x <*> y)
    question17 eq1 = 
        cong (x <*>) eq1
    
    0 question18 : {xO : b} -> Owl xO -> {theta : b} -> SageBird theta -> SageBird $ xO<*>theta
    question18 owl sage x = 
        let eq1 = owl theta x
            eq2 = cong (x<*>) eq1
            eq3 = cong (x <*>) $ sym $ sage x
        in trans eq1 $ sym $ trans eq2 eq3
    
    0 question19 : {xO : b} -> Owl xO -> {theta : b} -> SageBird theta -> SageBird $ theta<*>xO
    question19 owl sage x = 
        let eq1 = cong (<*> x) $ sage xO
            eq2 = owl (theta <*> xO) x
        in trans eq1 eq2
    
    0 question20 : {xO : b} -> Owl xO -> {xA : b} -> Fond xO xA -> SageBird xA
    question20 owl eq1 x = 
        let eq2 = sym $ cong (<*> x) eq1
            eq3 = owl xA x
        in trans eq2 eq3
    
    0 ChoosyBird : b -> Type 
    ChoosyBird xA = (xB : b) -> Fond xA xB -> SageBird xB

    0 question21 : {xA : b} -> ChoosyBird xA -> {theta : b} -> SageBird theta -> SageBird $ theta<*>xA
    question21 choosy sage x = 
        let eq1 = cong (<*> x) $ sage xA
            eq2 = (choosy (theta <*> xA) $ sym $ sage xA) x
        in trans eq1 $ trans (sym eq1) eq2
    
    0 Similar : b -> b -> Type 
    Similar xA1 xA2 = (x : b) -> xA1 <*> x = xA2 <*> x 

    0 question22 : {xO : b} -> Owl xO -> {theta : b} -> SageBird theta -> Similar theta $ xO<*>theta
    question22 owl sage x = 
        let eq1 = sage x 
            eq2 = owl theta x
        in trans eq1 $ sym eq2
    
    0 Extensional : Type 
    Extensional = (xA1 : b) -> (xA2 : b) -> Similar xA1 xA2 -> xA1 = xA2 

    0 question23 : Extensional -> {xO : b} -> Owl xO -> {theta : b} -> SageBird theta -> Fond xO theta
    question23 extensional owl sage = 
        extensional (xO <*> theta) theta $ \x => sym $ question22 owl sage x
    
