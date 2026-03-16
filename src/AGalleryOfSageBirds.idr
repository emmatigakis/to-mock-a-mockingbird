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
