module TheMasterForest

data SKIExpr : Type where
    Var : Char -> SKIExpr
    S : SKIExpr
    K : SKIExpr
    I :SKIExpr
    (<*>) : SKIExpr -> SKIExpr ->SKIExpr

varOccurs : Char -> SKIExpr -> Bool
varOccurs c (Var d) = c == d
varOccurs c S = False
varOccurs c K = False
varOccurs c I = False
varOccurs c (x <*> y) = (varOccurs c x) || (varOccurs c y)

alphaEliminate : Char -> SKIExpr -> SKIExpr
alphaEliminate c (Var d) = 
    if c == d then I --principles 1 
    else K <*> (Var d) --principles 2
alphaEliminate c S = K <*> S --principle 2
alphaEliminate c K = K <*> K --principle 2
alphaEliminate c I = K <*> I --principle 2
alphaEliminate c x@(y <*> z) = 
    if varOccurs c x then 
        if varOccurs c y then S <*> (alphaEliminate c y) <*> (alphaEliminate c z) --principle 4
        else 
            case z of
                 (Var d) => y -- principle 3
                 _ => S <*> (alphaEliminate c y) <*> (alphaEliminate c z) --principle 4
    else K <*> x --principle 2

eliminate : List Char -> SKIExpr ->SKIExpr
eliminate [] x = x
eliminate (c :: cs) x = eliminate cs $ alphaEliminate c x

expr = Var 'y' <*> Var 'x'