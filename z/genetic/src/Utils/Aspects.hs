module Utils.Aspects where

import Data.Set as S   (fromList)
import Data.Map      hiding (map)
import Control.Exception (assert)

type Name                = String

-- TODO: I think, it is possible to avoid strings
-- and use typed tags instead (with `Aspected a' as parameter)
-- UP:   Maybe, vararg/polyvariadic functions idiom can help?

newtype ConcreteSchema a = ConcreteSchema (Map Name Aspect    )               deriving Show
newtype AbstractSchema a = AbstractSchema (Map Name AspectType)               deriving Show

data AspectType = ABoolType  | ACharType  | AStringType    | AIntegerType     deriving Show
data Aspect     = ABool Bool | AChar Char | AString String | AInteger Integer deriving Show

class Aspected a where
    schema         :: AbstractSchema a
    assembleRaw    :: ConcreteSchema a -> a
    disassembleRaw :: a -> ConcreteSchema a

check :: AbstractSchema a -> ConcreteSchema a -> Bool
check (AbstractSchema as) (ConcreteSchema cs) =
    let ks  =              keys as
        aks = S.fromList $ keys as
        cks = S.fromList $ keys cs
    in  (&&) (aks == cks) $
        all correct' $ map (\k -> (as ! k, cs ! k)) ks
    where
        correct' = uncurry correct

        correct :: AspectType -> Aspect -> Bool
        correct ABoolType    (ABool    _) = True
        correct ACharType    (AChar    _) = True
        correct AStringType  (AString  _) = True
        correct AIntegerType (AInteger _) = True
        correct _             _           = False

assemble    :: Aspected a => ConcreteSchema a -> a
assemble    cs = let x = assembleRaw cs
                 in assert (check schema cs) x

disassemble :: Aspected a => a -> ConcreteSchema a
disassemble x  = let cs = disassembleRaw x
                 in assert (check schema cs) cs

-- Boilerplate:

type MapModification a b = Map a b -> Map a b
withSchema  :: Aspected a => MapModification Name Aspect -> ConcreteSchema a -> ConcreteSchema a
withSchema f (ConcreteSchema m) = ConcreteSchema $ f m

newAspect   :: Aspected a => Name -> Aspect  -> ConcreteSchema a -> ConcreteSchema a
newAspect k a = withSchema (insert k a)

newBool     :: Aspected a => Name -> Bool    -> ConcreteSchema a -> ConcreteSchema a
newBool   k b = newAspect k $ ABool b

dropFlag    :: Aspected a => Name            -> ConcreteSchema a -> ConcreteSchema a
dropFlag  k   = newBool k False

setFlag     :: Aspected a => Name            -> ConcreteSchema a -> ConcreteSchema a
setFlag   k   = newBool k True

newChar     :: Aspected a => Name -> Char    -> ConcreteSchema a -> ConcreteSchema a
newChar   k c = newAspect k $ AChar c

newString   :: Aspected a => Name -> String  -> ConcreteSchema a -> ConcreteSchema a
newString k s = newAspect k $ AString s

newInteger  :: Aspected a => Name -> Integer -> ConcreteSchema a -> ConcreteSchema a
newInteger k i = newAspect k $ AInteger i
