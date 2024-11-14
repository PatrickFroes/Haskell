import Control.Monad (replicateM)
import Data.List (nub)
import Data.Char (isSpace)

-- Tipo de dados para representar expressões lógicas proposicionais
data Expressao
    = Variavel Char                     -- Variável proposicional
    | Nao Expressao                     -- Negação
    | E Expressao Expressao             -- Conjunção
    | Ou Expressao Expressao            -- Disjunção
    | Implica Expressao Expressao       -- Implicação
    | Bicondicional Expressao Expressao -- Bicondicional
    deriving (Eq, Show)

-- Função que avalia uma expressão lógica em variáveis
avaliar :: [(Char, Bool)] -> Expressao -> Bool
avaliar ambiente (Variavel x) = case lookup x ambiente of
    Just valor -> valor
    Nothing -> False
avaliar ambiente (Nao e) = not (avaliar ambiente e)
avaliar ambiente (E e1 e2) = avaliar ambiente e1 && avaliar ambiente e2
avaliar ambiente (Ou e1 e2) = avaliar ambiente e1 || avaliar ambiente e2
avaliar ambiente (Implica e1 e2) = not (avaliar ambiente e1) || avaliar ambiente e2
avaliar ambiente (Bicondicional e1 e2) = avaliar ambiente e1 == avaliar ambiente e2

-- Gera todas as interpretações possíveis para um conjunto de variáveis ("Tabela verdade")
todasInterpretes :: [Char] -> [[(Char, Bool)]]
todasInterpretes variaveis = map (zip variaveis) (replicateM (length variaveis) [True, False])

-- Classifica uma expressão como tautologia, contradição ou contingente
classificarExpressao :: Expressao -> String
classificarExpressao expressao =
    let variaveis = nub (coletarVariaveis expressao)
        interpretacoes = todasInterpretes variaveis
        resultados = map (\i -> avaliar i expressao) interpretacoes
    in case (all id resultados, any id resultados) of
        (True, _) -> "A expressão é uma Tautologia (verdadeira em todas as interpretações)"
        (False, False) -> "A expressão é uma Contradição (falsa em todas as interpretações)"
        _ -> "A expressão é Contingente (verdadeira em algumas interpretações e falsa em outras)"

-- Pega todas as variáveis em uma expressão
coletarVariaveis :: Expressao -> [Char]
coletarVariaveis (Variavel x) = [x]
coletarVariaveis (Nao e) = coletarVariaveis e
coletarVariaveis (E e1 e2) = coletarVariaveis e1 ++ coletarVariaveis e2
coletarVariaveis (Ou e1 e2) = coletarVariaveis e1 ++ coletarVariaveis e2
coletarVariaveis (Implica e1 e2) = coletarVariaveis e1 ++ coletarVariaveis e2
coletarVariaveis (Bicondicional e1 e2) = coletarVariaveis e1 ++ coletarVariaveis e2

-- Função para converter de expressão em Forma Normal Conjuntiva (FNC)
paraFNC :: Expressao -> Expressao
paraFNC (Nao (E e1 e2)) = Ou (Nao (paraFNC e1)) (Nao (paraFNC e2))
paraFNC (Nao (Ou e1 e2)) = E (Nao (paraFNC e1)) (Nao (paraFNC e2))
paraFNC (E e1 e2) = E (paraFNC e1) (paraFNC e2)
paraFNC (Ou e1 e2) = Ou (paraFNC e1) (paraFNC e2)
paraFNC (Implica e1 e2) = Ou (Nao (paraFNC e1)) (paraFNC e2)
paraFNC (Bicondicional e1 e2) = E (Implica (paraFNC e1) (paraFNC e2)) (Implica (paraFNC e2) (paraFNC e1))
paraFNC e = e

-- Tenta converter uma expressão em um conjunto de cláusulas de Horn
paraClausulasDeHorn :: Expressao -> Either String [Expressao]
paraClausulasDeHorn expressao = 
    let expressaoFNC = paraFNC expressao
    in if eDeHorn expressaoFNC
       then Right (extrairClausulas expressaoFNC)
       else Left "A expressão não pode ser representada em cláusulas de Horn"

-- Verifica se uma expressão em FNC é uma expressão de Horn
eDeHorn :: Expressao -> Bool
eDeHorn (Ou (Nao _) _) = True
eDeHorn (E e1 e2) = eDeHorn e1 && eDeHorn e2
eDeHorn _ = False

-- Extrai cláusulas de uma expressão em FNC
extrairClausulas :: Expressao -> [Expressao]
extrairClausulas (E e1 e2) = extrairClausulas e1 ++ extrairClausulas e2
extrairClausulas e = [e]

-- Função de análise (parser) para interpretar uma string em uma expressão lógica
parseExpressao :: String -> Expressao
parseExpressao entrada = 
    let (expressao, _) = parseOu (filter (not . isSpace) entrada)
    in expressao

-- Funções de parsing para cada operador, seguindo a precedência
parseOu :: String -> (Expressao, String)
parseOu s = 
    let (e1, rest) = parseE s
    in case rest of
        'v':xs -> let (e2, rest') = parseOu xs in (Ou e1 e2, rest')
        _      -> (e1, rest)

parseE :: String -> (Expressao, String)
parseE s =
    let (e1, rest) = parseNao s
    in case rest of
        '^':xs -> let (e2, rest') = parseE xs in (E e1 e2, rest')
        _      -> (e1, rest)

parseNao :: String -> (Expressao, String)
parseNao ('~':s) = 
    let (e, rest) = parseNao s
    in (Nao e, rest)
parseNao s = parseImplica s

parseImplica :: String -> (Expressao, String)
parseImplica s =
    let (e1, rest) = parseBicondicional s
    in case rest of
        '=':'>':xs -> let (e2, rest') = parseImplica xs in (Implica e1 e2, rest')
        _          -> (e1, rest)

parseBicondicional :: String -> (Expressao, String)
parseBicondicional s =
    let (e1, rest) = parseTermo s
    in case rest of
        '<':'=':'>':xs -> let (e2, rest') = parseBicondicional xs in (Bicondicional e1 e2, rest')
        _              -> (e1, rest)

-- Parsing de termos, incluindo parênteses e variáveis
parseTermo :: String -> (Expressao, String)
parseTermo ('(':s) = 
    let (e, rest) = parseOu s
    in case rest of
        ')':xs -> (e, xs)
        _      -> error "Erro de sintaxe: Parêntese não fechado"
parseTermo (x:xs)
    | x >= 'A' && x <= 'Z' = (Variavel x, xs)  -- Variáveis de A-Z
    | otherwise = error $ "Erro de sintaxe: Caractere inválido: " ++ [x]
parseTermo [] = error "Erro de sintaxe: Expressão incompleta"

-- Exibe a expressão formatada em LaTeX
expressaoParaLatex :: Expressao -> String
expressaoParaLatex (Variavel x) = [x]
expressaoParaLatex (Nao e) = "¬" ++ expressaoParaLatex e
expressaoParaLatex (E e1 e2) = "(" ++ expressaoParaLatex e1 ++ " ∧ " ++ expressaoParaLatex e2 ++ ")"
expressaoParaLatex (Ou e1 e2) = "(" ++ expressaoParaLatex e1 ++ " ∨ " ++ expressaoParaLatex e2 ++ ")"
expressaoParaLatex (Implica e1 e2) = "(" ++ expressaoParaLatex e1 ++ " → " ++ expressaoParaLatex e2 ++ ")"
expressaoParaLatex (Bicondicional e1 e2) = "(" ++ expressaoParaLatex e1 ++ " ↔ " ++ expressaoParaLatex e2 ++ ")"

-- Função principal para interação
main :: IO ()
main = do
    let inputExpressao = "(B^C)=>A" 
    let expressao = parseExpressao inputExpressao
    putStrLn $ "Expressão lógica: " ++ inputExpressao
    putStrLn $ "Expressão em LaTeX: $$" ++ expressaoParaLatex expressao ++ "$$"
    putStrLn $ "Classificação: " ++ classificarExpressao expressao
    let expressaoFNC = paraFNC expressao
    putStrLn $ "Forma Normal Conjuntiva (FNC): $$" ++ expressaoParaLatex expressaoFNC ++ "$$"
    case paraClausulasDeHorn expressao of
        Right clausulas -> do
            putStrLn "Cláusula de Horn:"
            mapM_ (putStrLn . expressaoParaLatex) clausulas
            
