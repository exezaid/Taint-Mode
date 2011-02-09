{-# OPTIONS -fglasgow-exts -fallow-undecidable-instances #-}

module Lattice where

class (Eq a, Show a) => Lattice a where
  label_top :: a
  label_bottom :: a
  label_join :: a -> a -> a
  label_meet :: a -> a -> a
  label_leq :: a -> a -> Bool

data TriLabel = LOW | MEDIUM | HIGH 
		deriving (Eq, Show)

instance Lattice TriLabel where
  label_top = HIGH
  label_bottom = LOW
  label_join x y = if label_leq x y then y else x
  label_meet x y = if label_leq x y then x else y
  label_leq LOW _ = True
  label_leq MEDIUM LOW = False
  label_leq MEDIUM _ = True
  label_leq HIGH HIGH = True
  label_leq HIGH _ = False

data Label l = Lab l | LVar String
     deriving (Eq, Show)

data SecType l = SecLabel (Label l) | Ref (SecType l) (Label l) | Pair (SecType l) (SecType l) | 
                 SecHigh | SecEither (SecType l) (SecType l) (Label l) | SecVar String
		deriving (Eq, Show)

class (Lattice l, Eq (a l), Show (a l)) => MultiLattice a l where
  mlabel_top :: a l -> a l
  mlabel_top = mlabel_label label_top
  mlabel_bottom :: a l -> a l
  mlabel_bottom = mlabel_label label_bottom
  mlabel_label :: l -> a l -> a l
  mlabel_join :: a l -> a l -> a l
  mlabel_meet :: a l -> a l -> a l
  mlabel_leq :: a l -> a l -> Bool
  -- extract identity label to represent the complex security label
  mextract :: a l -> l
  mext_join :: a l -> l
  mext_meet :: a l -> l
  mlabel_tag :: a l -> l -> a l
  mlabel_decl :: a l -> a l -> l -> a l

{-
  Because of mlabel_leq for Ref has invariant in the content,
  each Ref of the same content forms a lattice.
-}
instance Lattice l => MultiLattice SecType l where
  mlabel_label l (SecLabel _) = SecLabel (Lab l)
  mlabel_label l (Ref t _) = Ref t (Lab l)
  mlabel_label l (Pair t1 t2) = Pair (mlabel_label l t1) (mlabel_label l t2)
  mlabel_label l SecHigh = SecHigh
  mlabel_label l (SecEither t1 t2 _) = SecEither (mlabel_label l t1) (mlabel_label l t2) (Lab l)

  mlabel_join (SecLabel (Lab l1)) (SecLabel (Lab l2)) = SecLabel (Lab (label_join l1 l2))
  mlabel_join (Ref t1 (Lab l1)) (Ref t2 (Lab l2)) = if t1 /= t2
                                                      then error $ "Ref : no join defined."
                                                      else Ref t1 (Lab (label_join l1 l2))
  mlabel_join (Pair s1 t1) (Pair s2 t2) = Pair (mlabel_join s1 s2) (mlabel_join t1 t2)
  mlabel_join SecHigh SecHigh = SecHigh
  mlabel_join (SecEither s1 t1 (Lab l1)) (SecEither s2 t2 (Lab l2)) = 
                                SecEither (mlabel_join s1 s2) (mlabel_join t1 t2) (Lab (label_join l1 l2))

  mlabel_meet (SecLabel (Lab l1)) (SecLabel (Lab l2)) = SecLabel (Lab (label_meet l1 l2))
  mlabel_meet (Ref t1 (Lab l1)) (Ref t2 (Lab l2)) = if t1 /= t2
                                                      then error $ "Ref : no meet defined."
                                                      else Ref t1 (Lab (label_meet l1 l2))
  mlabel_meet (Pair s1 t1) (Pair s2 t2) = Pair (mlabel_meet s1 s2) (mlabel_meet t1 t2)
  mlabel_meet SecHigh SecHigh = SecHigh
  mlabel_meet (SecEither s1 t1 (Lab l1)) (SecEither s2 t2 (Lab l2)) =
                                SecEither (mlabel_meet s1 s2) (mlabel_meet t1 t2) (Lab (label_meet l1 l2))

  mlabel_leq (SecLabel (Lab l1)) (SecLabel (Lab l2)) = label_leq l1 l2
  mlabel_leq SecHigh (SecLabel (Lab l2)) = label_leq label_top l2
  mlabel_leq (SecLabel (Lab l1)) SecHigh = label_leq l1 label_top
  mlabel_leq (Ref st1 (Lab lr1)) (Ref st2 (Lab lr2)) = label_leq lr1 lr2 && mlabel_leq st1 st2 && mlabel_leq st2 st1
  mlabel_leq SecHigh (Ref st2 (Lab lr2)) = (label_leq label_top lr2) && (mlabel_leq SecHigh st2)
  mlabel_leq (Ref st1 (Lab lr1)) SecHigh = (label_leq lr1 label_top) && (mlabel_leq st1 SecHigh)
  mlabel_leq (Pair s1 t1) (Pair s2 t2) = mlabel_leq s1 s2 && mlabel_leq t1 t2
  mlabel_leq SecHigh (Pair s2 t2) = mlabel_leq SecHigh s2 && mlabel_leq SecHigh t2
  mlabel_leq (Pair s1 t1) SecHigh = mlabel_leq s1 SecHigh && mlabel_leq t1 SecHigh
  mlabel_leq (SecEither s1 t1 (Lab l1)) (SecEither s2 t2 (Lab l2)) = 
                                    mlabel_leq s1 s2 && mlabel_leq t1 t2 && label_leq l1 l2
  mlabel_leq (SecEither s1 t1 (Lab l1)) SecHigh = 
                                    mlabel_leq s1 SecHigh && mlabel_leq t1 SecHigh && label_leq l1 label_top
  mlabel_leq SecHigh (SecEither s1 t1 (Lab l2)) = 
                                    mlabel_leq SecHigh s1 && mlabel_leq SecHigh t1 && label_leq label_top l2
  mlabel_leq SecHigh SecHigh = True
  mlabel_leq t1 t2 = error $ "undefined relation : " ++ (show t1) ++ " and " ++ (show t2) 

  mextract (SecLabel (Lab l)) = l
  mextract (Ref s (Lab l)) = l
  mextract (Pair s t) = (mextract s) `label_join` (mextract t)
  mextract SecHigh = label_top
  mextract (SecEither s t (Lab l)) = l

  mext_join s = propLeaf ext label_join s

  mext_meet s = propLeaf ext label_meet s

  mlabel_tag (SecLabel _) l = SecLabel (Lab l)
  mlabel_tag (Ref s _) l = Ref s (Lab l)
  mlabel_tag (Pair s1 s2) l = Pair (mlabel_tag s1 l) (mlabel_tag s2 l)
  mlabel_tag (SecEither s1 s2 _) l = SecEither (mlabel_tag s1 l) (mlabel_tag s2 l) (Lab l)
  mlabel_tag SecHigh l = SecHigh

  mlabel_decl SecHigh s_out l = s_out
  mlabel_decl (SecLabel (Lab l1)) _ l = SecLabel (Lab (if label_leq l1 l then l1 else l))
  mlabel_decl (Ref s (Lab l1)) (Ref s' _) l = Ref (mlabel_decl s s' l) (Lab (if label_leq l1 l then l1 else l))
  mlabel_decl (Pair s1 s2) (Pair s1' s2') l = Pair (mlabel_decl s1 s1' l) (mlabel_decl s2 s2' l)
  mlabel_decl (SecEither s1 s2 (Lab l1)) (SecEither s1' s2' _) l = 
              SecEither (mlabel_decl s1 s1' l) (mlabel_decl s2 s2' l) (Lab (if label_leq l1 l then l1 else l))

ext (SecLabel (Lab l)) = l
ext SecHigh = label_top
ext (SecVar _) = undefined

--------------------------------------------------------
-- Check if a (SecType l) contains a property at leaf --
--------------------------------------------------------
propLeaf :: (SecType l -> a) -> (a -> a -> a) -> SecType l -> a
propLeaf f con v@(SecVar _) = f v
propLeaf f con v@(SecHigh) = f v
propLeaf f con v@(SecLabel _) = f v
propLeaf f con (Ref t l) = (propLeaf f con t) `con` (f (SecLabel l))
propLeaf f con (Pair t1 t2) = (propLeaf f con t1) `con` (propLeaf f con t2)
propLeaf f con (SecEither t1 t2 l) = (propLeaf f con t1) `con` (propLeaf f con t2) `con` (f (SecLabel l))
--propLeaf _ _ _ = error "impossible structure in propLeaf."


class (Lattice l, MultiLattice a l) => Guard a l where
  label_guard :: a l -> a l -> Bool
  label_gsleql :: a l -> a l -> Bool
  label_glleqs :: a l -> a l -> Bool

instance (Lattice l, MultiLattice SecType l) => Guard SecType l where
  label_guard (SecLabel (Lab l)) s = label_leq l (mextract s)
  label_gsleql s (SecLabel (Lab l)) = label_leq (mext_join s) l
  label_glleqs (SecLabel (Lab l)) s = label_leq l (mext_meet s)
