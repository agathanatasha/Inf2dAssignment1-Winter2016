-- Inf2D Assignment 1 (Last updated: 25 Jan 2016)

-- Good Scholarly Practice
-- Please remember the University requirement as regards all assessed work for credit. 
-- Details about this can be found at:
-- http://www.ed.ac.uk/academic-services/students/undergraduate/discipline/academic-misconduct
-- and at:
-- http://web.inf.ed.ac.uk/infweb/admin/policies/academic-misconduct
-- Furthermore, you are required to take reasonable measures to protect your assessed work from 
-- unauthorised access.For example, if you put any such work on a public repository then you must 
-- set access permissions appropriately (generally permitting access only to yourself, or your 
-- group in the case of group practicals).

module Inf2d where
import Data.List
import Debug.Trace
import Data.Ord
import Data.Maybe
import System.TimeIt
import Control.Exception.Base
import System.IO.Unsafe
-- Type synonyms for the data structures
-- Symbols are strings (a negative sign as the first character represents a negated symbol)
type Symbol = String
-- Clause = a disjuntion of symbols
type Clause = [Symbol] 
-- Sentence = Statements. This is a list of a list of symbols
type Sentence = [[Symbol]] 
-- Models are represented as a list of (Symbol,Boolean) tuples
type Model = [(Symbol, Bool)]
-- The knowledge base is represented as a list of statements
type KB = [Sentence]

-----------------------------------------------
-- STUDENT MATRICULATION NUMBER: s1575257
-----------------------------------------------
studentId::String
studentId = "s1575257"

--------------------------------------------------
-- ASSIGNMENT TASKS
-- Refer to assignment sheet for details of tasks
--------------------------------------------------

----------TASK 1: REPRESENTATION (2 marks)----------------------------------------------------------
wumpusFact::Sentence
wumpusFact = [["-B11", "P11", "P22", "P31"], ["-P11", "B11"], ["-P22", "B11"], ["-P31", "B11"]]

----------TASK 2: GENERAL HELPER FUNCTIONS (10 marks)-----------------------------------------------

-- Finds the assigned literal to a symbol from a given model
lookupAssignment :: Symbol -> Model -> Maybe Bool
lookupAssignment symbol [] = Nothing
lookupAssignment symbol (x:xs)
  |symbol == fst x = Just(snd x)
  |otherwise = lookupAssignment symbol xs

-- Negate a symbol
negateSymbol :: Symbol -> Symbol
negateSymbol symbol 
  | isNegated symbol = tail symbol
  | otherwise = "-" ++ symbol

-- For a given symbol, this function checks if it is negated(i.e., has a negation sign).
isNegated :: Symbol -> Bool
isNegated symbol =
  if (isPrefixOf "-" symbol) then True else False

-- This function takes a symbol and returns an Symbol without any negation sign if the original 
-- symbol had one.
getUnsignedSymbol :: Symbol -> Symbol
getUnsignedSymbol symbol =
  if isNegated symbol then tail symbol else symbol

-- Gets a list of all symbols in for all given sentences
getSymbols :: [Sentence] -> [Symbol]
getSymbols stmts = removeDuplicate(concat(concat stmts))

-- Remove duplicate symbols in a list of symbols
removeDuplicate :: [Symbol] -> [Symbol]
removeDuplicate = rdHelper []
    where rdHelper seen [] = seen
          rdHelper seen (x:xs)
              | x `elem` seen = rdHelper seen xs
              | otherwise = rdHelper (seen ++ [x]) xs

----------TASK 3: TRUTH TABLE ENUMERATION AND ENTAILMENT (40 marks)---------------------------------

-- Function takes as input a list of symbols, and returns a list of models (all possible assignment 
-- of True or False to the symbols.)
generateModels :: [Symbol] -> [Model]
generateModels [] = []
generateModels (a:as) = [(a,b) : r | b <- [True, False], r <- generateModels as]

-- This function evaluates the truth value of a propositional sentence using the symbols 
-- assignments in the model.
pLogicEvaluate :: Sentence -> Model -> Bool
pLogicEvaluate [] model = False
pLogicEvaluate [x] model = clauseEvaluate x model
pLogicEvaluate (x:xs) model =  and ( [clauseEvaluate x model] ++ [pLogicEvaluate xs model] )

-- Helper function for pLogicEvaluate, evaluate the truth value of a propositional
-- clause using symbols assignment in the model.
clauseEvaluate :: Clause -> Model -> Bool
clauseEvaluate [] model = False
clauseEvaluate (x:xs) model = or ( catMaybes([lookupAssignment x model]) ++ [clauseEvaluate xs model] )


-- This function checks the truth value of list of a propositional sentence using the symbols 
-- assignments in the model. It returns true only when all sentences in the list are true.
plTrue :: [Sentence]-> Model -> Bool 
plTrue [] model = False
plTrue [x] model = pLogicEvaluate x model
plTrue (x:xs) model = and ( [pLogicEvaluate x model] ++ [plTrue xs model] )

-- This function takes as input a knowledgebase (i.e. a list of propositional sentences), 
-- a query (i.e. a propositional sentence), and a list of symbols.
-- IT recursively enumerates the models of the domain using its symbols to check if there 
-- is a model that satisfies the knowledge base and the query. It returns a list of all such models.generateModels symbols
ttCheckAll :: [Sentence] -> Sentence -> [Symbol] -> [Model]
ttCheckAll kb query symbol = ttCheckAll' kb query symbol []

-- Helper function for ttCheckAll. Takes knowledgebase, query, list of symbols and model as input
ttCheckAll' :: [Sentence] -> Sentence -> [Symbol] -> Model -> [Model]
ttCheckAll' kb query [] model = if plTrue kb model && pLogicEvaluate query model then [model] else []
ttCheckAll' kb query (x:xs) model = ttCheckAll' kb query xs (model ++ [(x,True)]) ++ ttCheckAll' kb query xs (model ++ [(x,False)])


-- This function determines if a model satisfes both the knowledge base and the query, returning
-- true or false.
ttEntails :: [Sentence] -> Sentence -> Bool
ttEntails kb query = let symbols = removeDuplicate(getSymbols kb) ++ (getSymbols [query])
                         model = ttCheckAll kb query symbols
                     in ttEntails' kb query model
                        
-- Old Helper function for ttEntails. It recursively check if model in models satisfies both the
-- knowledge base and the query, returning True or False.
-- ttEntails' :: [Sentence] -> Sentence -> [Model] -> Bool
-- ttEntails' kb query [] = False
-- ttEntails' kb query (x:xs)
--   | plTrue kb x = pLogicEvaluate query x
--   | otherwise = True
-- ttEntails' kb query (x:xs) = ttEntails' kb query xs

-- New Helper function for ttEntails. It recursively check if model in models satisfies both the
-- knowledge base and the query, returning True or False. 20 Feb 2017
ttEntails' :: [Sentence] -> Sentence -> [Model] -> Bool
ttEntails' kb query [] = False
ttEntails' kb query (x:xs)
  | xs == [] && plTrue kb x && pLogicEvaluate query x = True
  | plTrue kb x && pLogicEvaluate query x = ttEntails' kb query xs
  | otherwise = False

-- This function determines if a model satisfes both the knowledge base and the query. 
-- It returns a list of all models for which the knowledge base entails the query.
ttEntailsModels :: [Sentence] -> Sentence -> [Model]
ttEntailsModels kb query = let symbols = getSymbols kb in ttCheckAll kb query symbols


----------TASK 4: DPLL (43 marks)-------------------------------------------------------------------

-- The early termination function checks if a sentence is true or false even with a 
-- partially completed model.
earlyTerminate :: Sentence -> Model -> Bool
earlyTerminate sentence model = pLogicEvaluate sentence model

-- This function finds pure symbol, i.e, a symbol that always appears with the same "sign" in all 
-- clauses.
-- It takes a list of symbols, a list of clauses and a model as inputs. 
-- It returns Just a tuple of a symbol and the truth value to assign to that
-- symbol. If no pure symbol is found, it should return Nothing

-- findPureSymbol :: [Symbol] -> [Clause] -> Model -> Maybe (Symbol, Bool)
-- findPureSymbol symbols clauses model = Nothing
-- findPureSymbol (x:xs) clauses model =
--   let a = filter ((==x).fst) model in if a == [] then if negateSymbol x `notElem` concat clauses
--                                                       then if isNegated x then Just(x,False)
--                                                            else Just(x,True)
--                                                       else Nothing
--                                       else Nothing
-- findPureSymbol(x:xs) clauses model = findPureSymbol xs clauses model

--v2 findPureSymbol
findPureSymbol :: [Symbol] -> [Clause] -> Model -> Maybe (Symbol, Bool)
findPureSymbol symbols [] model  = Nothing
findPureSymbol symbols clauses model = listToMaybe [ (x,True) | x <- concat clauses,lookup x model == Nothing && negateSymbol x `notElem` concat clauses]

-- This function finds a unit clause from a given list of clauses and a model of assignments.
-- It returns Just a tuple of a symbol and the truth value to assign to that symbol. If no new unit  
-- clause is found, it should return Nothing.
findUnitClause :: [Clause] -> Model -> Maybe (Symbol, Bool)
findUnitClause [] model = Nothing
findUnitClause (x:xs) model
  | length x == 1 && not( isJust (lookup (concat x) model)) = listToMaybe [(concat x,True)]
  | oneInClause x model /= Nothing = oneInClause x model
  | otherwise = findUnitClause xs model

-- Helper function for findUnitClause,  return Just a tuple of a symbol and the truth value if all literals
-- but one are already assigned false by the model. If it is not the case, Nothing is returned.
oneInClause :: Clause -> Model -> Maybe (Symbol, Bool)
oneInClause [] model = Nothing
oneInClause clause model 
  | (length element)  == 1 && length rest == length clause - 1 = listToMaybe[((clause !! head element), True)]
  | otherwise = Nothing
  where lst = [lookup z model | z <- clause ]
        element = elemIndices Nothing lst
        rest = elemIndices (Just False) lst
        
-- This function check the satisfability of a sentence in propositional logic. It takes as input a 
-- list of clauses in CNF, a list of symbols for the domain, and model. 
-- It returns true if there is a model which satises the propositional sentence. 
-- Otherwise it returns false.
dpll :: [Clause] -> [Symbol] -> Model -> Bool
dpll clauses symbols model
  
  | not (null p) = dpll clauses (filter (/= (fst (p !!0 ))) symbols) (p++model)
  | not (null q) = dpll clauses (filter (/= (fst (q !!0 ))) symbols) (q++model)
  | not (null clauses) && null symbols = earlyTerminate clauses model
  | all (== True) evalclauses = True
  | otherwise =  dpll clauses xs ((s, True):model) || dpll clauses xs ((s, False):model)
  where evalclauses = [clauseEvaluate a model | a <- clauses]
        p = maybeToList (findPureSymbol symbols clauses model)
        q = maybeToList (findUnitClause clauses model)
        s = head symbols
        xs = tail symbols

-- This function serves as the entry point to the dpll function. It takes a list clauses in CNF as 
-- input and returns true or false. 
-- It uses the dpll function above to determine the satisability of its input sentence.
dpllSatisfiable :: [Clause] -> Bool
dpllSatisfiable clauses = dpll clauses (removeDuplicate [getUnsignedSymbol x | x <- concat clauses]) []

----------TASK 5: EVALUATION (5 marks)--------------------------------------------------------------
-- EVALUATION
-- a knowledge base (i.e. a sentence in propositional 
-- logic), and a query sentence. Both items should have their clauses in CNF representation 
-- and should be assigned to the following respectively:
evalKB :: [Sentence]
evalKB = [[["-P11"],["Q21"]],[["P21"],["Q21"]]]

evalQuery :: Sentence
evalQuery = [["P21", "Q21", "-P11"], ["Q21", "-P21"], ["P11", "-P21"]]


-- RUNTIMES
-- Enter the average runtimes of the ttEntails and dpllSatisable functions respectively
runtimeTtEntails :: Double
runtimeTtEntails = sum ([unsafePerformIO (timer (evaluate (ttEntails evalKB evalQuery))), unsafePerformIO (timer (evaluate (ttEntails evalKB evalQuery))), unsafePerformIO (timer (evaluate (ttEntails evalKB evalQuery))), unsafePerformIO (timer (evaluate (ttEntails evalKB evalQuery))), unsafePerformIO (timer (evaluate (ttEntails evalKB evalQuery)))])/5

runtimeDpll :: Double
runtimeDpll = (sum [unsafePerformIO (timer (evaluate (dpllSatisfiable evalQuery))), unsafePerformIO (timer (evaluate (dpllSatisfiable evalQuery))), unsafePerformIO (timer (evaluate (dpllSatisfiable evalQuery))), unsafePerformIO (timer (evaluate (dpllSatisfiable evalQuery))), unsafePerformIO (timer (evaluate (dpllSatisfiable evalQuery)))])/5

-- helper functions for the runtime functions
-- Take the IO function as input and evaluate its runtime
timer :: IO a -> IO Double
timer ioa = do
  (t,a) <- timeItT ioa
  return  t
