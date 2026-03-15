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
