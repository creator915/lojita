{-# OPTIONS --safe --cubical #-}
------------------------------------------------------------------------
-- Syntax.agda —— Agda 的具体语法：parser 吐出来的那棵树（Env.agda 的 Code E 在它上面）
--   由 agda-code-gen 从 Agda 源码（Agda.Syntax.Concrete / Common）生成，不要手改。
--   范围（Range）去掉，名字是字符串，构造子名照 Haskell；构造子与类型同名的加 ′。
--   只保留 parser 能产出的构造子：带抽象名、高亮、元变量的不在。
--   所有类型先给签名再给定义，所以它们是一个 mutual 块，顺序无关。
------------------------------------------------------------------------
module Syntax where

open import Cubical.Foundations.Prelude using (Type)
open import Cubical.Data.List.Base using (List; []; _∷_)
open import Cubical.Data.Maybe.Base using (Maybe; nothing; just)
open import Cubical.Data.Sum.Base using (_⊎_; inl; inr)
open import Cubical.Data.Sigma.Base using (_×_; _,_)
open import Cubical.Data.Unit.Base using (Unit; tt)
open import Cubical.Data.Bool.Base using (Bool; true; false)
open import Cubical.Data.Nat.Base using (ℕ)
open import Cubical.Data.Int.Base using (ℤ; pos; negsuc)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Char using (Char)
open import Agda.Builtin.Float using (Float)

-- 签名
data Module : Type
data Declaration : Type
data Expr : Type
data Pattern : Type
data Pragma : Type
data LHS : Type
data RHS (A : Type) : Type
data WhereClause (A : Type) : Type
data LamClause : Type
data DoStmt : Type
data Binder (A : Type) : Type
data BoundName : Type
data LamBinding (A : Type) : Type
data TypedBinding (A : Type) : Type
data TacticAttribute (A : Type) : Type
data BinderNameOrigin : Type
data FieldAssignment (A : Type) : Type
data ModuleAssignment : Type
data ModuleApplication : Type
data OpenShortHand : Type
data RecordDirective : Type
data PossiblyProjectionPattern : Type
data ImportDirective (A : Type) (B : Type) : Type
data Using (A : Type) (B : Type) : Type
data ImportedName (A : Type) (B : Type) : Type
data Renaming (A : Type) (B : Type) : Type
data AsName (A : Type) : Type
data RewriteEqn (A : Type) (B : Type) (C : Type) (D : Type) : Type
data Name : Type
data QName : Type
data NamePart : Type
data NameInScope : Type
data Literal : Type
data Fixity : Type
data Fixity' : Type
data FixityLevel : Type
data Associativity : Type
data NotationPart : Type
data BoundVariablePosition : Type
data Arg (A : Type) : Type
data ArgInfo : Type
data Named (A : Type) (B : Type) : Type
data WithHiding (A : Type) : Type
data WithOrigin (A : Type) : Type
data Hiding : Type
data Overlappable : Type
data OverlapMode : Type
data Modality : Type
data Relevance : Type
data Quantity : Type
data Cohesion : Type
data PolarityModality : Type
data ModalPolarity : Type
data Erased : Type
data Origin : Type
data Annotation : Type
data Lock : Type
data LockOrigin : Type
data RewriteAnn : Type
data Q0Origin : Type
data Q1Origin : Type
data QωOrigin : Type
data OriginRelevant : Type
data OriginIrrelevant : Type
data OriginShapeIrrelevant : Type
data Access : Type
data IsInstance : Type
data Induction : Type
data HasEta (A : Type) : Type
data Catchall : Type
data TerminationCheck (A : Type) : Type
data Occurrence : Type
data List1 (A : Type) : Type
data List2 (A : Type) : Type

data Module where
  Mod : QName → List Pragma → List Declaration → Module

data Declaration where
  TypeSig : ArgInfo → TacticAttribute Expr → Name → Expr → Declaration
  FieldSig : IsInstance → TacticAttribute Expr → Name → Arg Expr → Declaration
  Generalize : List Declaration → Declaration
  Field : List Declaration → Declaration
  FunClause : ArgInfo → LHS → RHS Expr → WhereClause (List Declaration) → Catchall → Declaration
  DataSig : Erased → Name → List (LamBinding (TypedBinding Expr)) → Expr → Declaration
  Data : Erased → Name → List (LamBinding (TypedBinding Expr)) → Expr → List Declaration → Declaration
  DataDef : Name → List (LamBinding (TypedBinding Expr)) → List Declaration → Declaration
  RecordSig : Erased → Name → List (LamBinding (TypedBinding Expr)) → Expr → Declaration
  RecordDef : Name → List RecordDirective → List (LamBinding (TypedBinding Expr)) → List Declaration → Declaration
  Record : Erased → Name → List RecordDirective → List (LamBinding (TypedBinding Expr)) → Expr → List Declaration → Declaration
  Infix : Fixity → List1 Name → Declaration
  Syntax : Name → List NotationPart → Declaration
  PatternSyn : Name → List (WithHiding Name) → Pattern → Declaration
  Mutual : List Declaration → Declaration
  InterleavedMutual : List Declaration → Declaration
  Abstract : List Declaration → Declaration
  Private : Origin → List Declaration → Declaration
  InstanceB : List Declaration → Declaration
  LoneConstructor : List Declaration → Declaration
  Macro : List Declaration → Declaration
  Postulate : List Declaration → Declaration
  Primitive : List Declaration → Declaration
  Open : QName → ImportDirective Name Name → Declaration
  Import : OpenShortHand → QName → ((AsName Name) ⊎ (List Expr)) → ImportDirective Name Name → Declaration
  ModuleMacro : Erased → Name → ModuleApplication → OpenShortHand → ImportDirective Name Name → Declaration
  Module′ : Erased → QName → List (TypedBinding Expr) → List Declaration → Declaration
  UnquoteDecl : List Name → Expr → Declaration
  UnquoteDef : List Name → Expr → Declaration
  UnquoteData : Name → List Name → Expr → Declaration
  Pragma′ : Pragma → Declaration
  Opaque : List Declaration → Declaration
  Unfolding : List QName → Declaration

data Expr where
  Ident : QName → Expr
  Lit : Literal → Expr
  QuestionMark : Maybe ℕ → Expr
  Underscore : Maybe String → Expr
  RawApp : List2 Expr → Expr
  App : Expr → Arg (Named (WithOrigin String) Expr) → Expr
  WithApp : Expr → List1 Expr → Expr
  HiddenArg : Named (WithOrigin String) Expr → Expr
  InstanceArg : Named (WithOrigin String) Expr → Expr
  Lam : List1 (LamBinding (TypedBinding Expr)) → Expr → Expr
  AbsurdLam : Hiding → Expr
  ExtendedLam : Erased → List1 LamClause → Expr
  Fun : Arg Expr → Expr → Expr
  Pi : List1 (TypedBinding Expr) → Expr → Expr
  Rec : List ((FieldAssignment Expr) ⊎ ModuleAssignment) → Expr
  RecUpdate : Expr → List (FieldAssignment Expr) → Expr
  RecWhere : List Declaration → Expr
  RecUpdateWhere : Expr → List Declaration → Expr
  Let : List1 Declaration → Maybe Expr → Expr
  Paren : Expr → Expr
  IdiomBrackets : Maybe QName → List Expr → Expr
  DoBlock : Maybe QName → List1 DoStmt → Expr
  Absurd : Expr
  As : Name → Expr → Expr
  Dot : Expr → Expr
  DoubleDot : Expr → Expr
  Quote : Expr
  QuoteTerm : Expr
  Tactic : Expr → Expr
  Unquote : Expr
  Equal : Expr → Expr → Expr
  Ellipsis : Expr
  Generalized : Expr → Expr

data Pattern where
  IdentP : Bool → QName → Pattern
  QuoteP : Pattern
  AppP : Pattern → Arg (Named (WithOrigin String) Pattern) → Pattern
  RawAppP : List2 Pattern → Pattern
  HiddenP : Named (WithOrigin String) Pattern → Pattern
  InstanceP : Named (WithOrigin String) Pattern → Pattern
  ParenP : Pattern → Pattern
  WildP : Pattern
  AbsurdP : Pattern
  AsP : Name → Pattern → Pattern
  DotP : PossiblyProjectionPattern → Expr → Pattern
  LitP : Literal → Pattern
  RecP : List (FieldAssignment Pattern) → Pattern
  EqualP : List1 (Expr × Expr) → Pattern
  EllipsisP : Maybe Pattern → Pattern
  WithP : Pattern → Pattern

data Pragma where
  OptionsPragma : List String → Pragma
  BuiltinPragma : String → QName → Pragma
  RewritePragma : List QName → Pragma
  ForeignPragma : String → String → Pragma
  CompilePragma : String → QName → String → Pragma
  StaticPragma : QName → Pragma
  InlinePragma : Bool → QName → Pragma
  ImpossiblePragma : List String → Pragma
  EtaPragma : QName → Pragma
  WarningOnUsage : QName → String → Pragma
  WarningOnImport : String → Pragma
  InjectivePragma : QName → Pragma
  InjectiveForInferencePragma : QName → Pragma
  DisplayPragma : Pattern → Expr → Pragma
  CatchallPragma : Pragma
  EtaEqualityPragma : Pragma
  TerminationCheckPragma : TerminationCheck Name → Pragma
  NoCoverageCheckPragma : Pragma
  NoPositivityCheckPragma : Pragma
  PolarityPragma : Name → List Occurrence → Pragma
  NoUniverseCheckPragma : Pragma
  NotProjectionLikePragma : QName → Pragma
  OverlapPragma : List QName → OverlapMode → Pragma

data LHS where
  LHS′ : Pattern → List (RewriteEqn Unit Name Pattern Expr) → List (Named Name (Arg Expr)) → LHS

data RHS A where
  AbsurdRHS : RHS A
  RHS′ : A → RHS A

data WhereClause A where
  NoWhere : WhereClause A
  AnyWhere : A → WhereClause A
  SomeWhere : Erased → Name → Access → A → WhereClause A

data LamClause where
  LamClause′ : List Pattern → RHS Expr → Catchall → LamClause

data DoStmt where
  DoBind : Pattern → Expr → List LamClause → DoStmt
  DoThen : Expr → DoStmt
  DoLet : List1 Declaration → DoStmt

data Binder A where
  Binder′ : Maybe Pattern → BinderNameOrigin → A → Binder A

data BoundName where
  BName : Name → Fixity' → TacticAttribute Expr → Bool → BoundName

data LamBinding A where
  DomainFree : Arg (Named (WithOrigin String) (Binder BoundName)) → LamBinding A
  DomainFull : A → LamBinding A

data TypedBinding A where
  TBind : List1 (Arg (Named (WithOrigin String) (Binder BoundName))) → A → TypedBinding A
  TLet : List1 Declaration → TypedBinding A

data TacticAttribute A where
  TacticAttribute′ : Maybe A → TacticAttribute A

data BinderNameOrigin where
  UserBinderName : BinderNameOrigin
  InsertedBinderName : BinderNameOrigin

data FieldAssignment A where
  FieldAssignment′ : Name → A → FieldAssignment A

data ModuleAssignment where
  ModuleAssignment′ : QName → List Expr → ImportDirective Name Name → ModuleAssignment

data ModuleApplication where
  SectionApp : List (TypedBinding Expr) → QName → List Expr → ModuleApplication
  RecordModuleInstance : QName → ModuleApplication

data OpenShortHand where
  DoOpen : OpenShortHand
  DontOpen : OpenShortHand

data RecordDirective where
  Induction′ : Induction → RecordDirective
  Constructor : Name → IsInstance → RecordDirective
  Eta : HasEta Unit → RecordDirective
  PatternOrCopattern : RecordDirective

data PossiblyProjectionPattern where
  CouldBeProjectionPattern : PossiblyProjectionPattern
  CannotBeProjectionPattern : PossiblyProjectionPattern

data ImportDirective A B where
  ImportDirective′ : Using A B → List (ImportedName A B) → List (Renaming A B) → Maybe Unit → ImportDirective A B

data Using A B where
  UseEverything : Using A B
  Using′ : List (ImportedName A B) → Using A B

data ImportedName A B where
  ImportedModule : B → ImportedName A B
  ImportedName′ : A → ImportedName A B

data Renaming A B where
  Renaming′ : ImportedName A B → ImportedName A B → Maybe Fixity → Renaming A B

data AsName A where
  AsName′ : A → AsName A

data RewriteEqn A B C D where
  Rewrite : List1 (A × D) → RewriteEqn A B C D
  Invert : A → List1 (Named B (C × D)) → RewriteEqn A B C D
  LeftLet : List1 (C × D) → RewriteEqn A B C D

data Name where
  Name′ : NameInScope → List1 NamePart → Name
  NoName : Name

data QName where
  Qual : Name → QName → QName
  QName′ : Name → QName

data NamePart where
  Hole : NamePart
  Id : String → NamePart

data NameInScope where
  InScope : NameInScope
  NotInScope : NameInScope

data Literal where
  LitNat : ℤ → Literal
  LitWord64 : ℕ → Literal
  LitFloat : Float → Literal
  LitString : String → Literal
  LitChar : Char → Literal

data Fixity where
  Fixity′ : FixityLevel → Associativity → Fixity

data Fixity' where
  Fixity'′ : Fixity → List NotationPart → Fixity'

data FixityLevel where
  Unrelated : FixityLevel
  Related : Float → FixityLevel

data Associativity where
  NonAssoc : Associativity
  LeftAssoc : Associativity
  RightAssoc : Associativity

data NotationPart where
  IdPart : String → NotationPart
  HolePart : Arg (Named (WithOrigin String) ℕ) → NotationPart
  VarPart : BoundVariablePosition → NotationPart
  WildPart : BoundVariablePosition → NotationPart

data BoundVariablePosition where
  BoundVariablePosition′ : ℕ → ℕ → BoundVariablePosition

data Arg A where
  Arg′ : ArgInfo → A → Arg A

data ArgInfo where
  ArgInfo′ : Hiding → Modality → Origin → Annotation → ArgInfo

data Named A B where
  Named′ : Maybe A → B → Named A B

data WithHiding A where
  WithHiding′ : Hiding → A → WithHiding A

data WithOrigin A where
  WithOrigin′ : Origin → A → WithOrigin A

data Hiding where
  Hidden : Hiding
  Instance : Overlappable → Hiding
  NotHidden : Hiding

data Overlappable where
  YesOverlap : Overlappable
  NoOverlap : Overlappable

data OverlapMode where
  Overlappable′ : OverlapMode
  Overlapping : OverlapMode
  Overlaps : OverlapMode
  DefaultOverlap : OverlapMode
  Incoherent : OverlapMode
  FieldOverlap : OverlapMode

data Modality where
  Modality′ : Relevance → Quantity → Cohesion → PolarityModality → Modality

data Relevance where
  Relevant : OriginRelevant → Relevance
  ShapeIrrelevant : OriginShapeIrrelevant → Relevance
  Irrelevant : OriginIrrelevant → Relevance

data Quantity where
  Quantity0 : Q0Origin → Quantity
  Quantity1 : Q1Origin → Quantity
  Quantityω : QωOrigin → Quantity

data Cohesion where
  Flat : Cohesion
  Continuous : Cohesion
  Sharp : Cohesion
  Squash : Cohesion

data PolarityModality where
  PolarityModality′ : ModalPolarity → ModalPolarity → ModalPolarity → PolarityModality

data ModalPolarity where
  UnusedPolarity : ModalPolarity
  StrictlyPositive : ModalPolarity
  Positive : ModalPolarity
  Negative : ModalPolarity
  MixedPolarity : ModalPolarity

data Erased where
  Erased′ : Q0Origin → Erased
  NotErased : QωOrigin → Erased

data Origin where
  UserWritten : Origin
  Inserted : Origin
  Reflected : Origin
  CaseSplit : Origin
  Substitution : Origin
  ExpandedPun : Origin
  Generalization : Origin
  ConversionFail : Origin
  RecordSelf : Origin

data Annotation where
  Annotation′ : Lock → RewriteAnn → Annotation

data Lock where
  IsNotLock : Lock
  IsLock : LockOrigin → Lock

data LockOrigin where
  LockOLock : LockOrigin
  LockOTick : LockOrigin

data RewriteAnn where
  IsNotRewrite : RewriteAnn
  IsRewrite : RewriteAnn

data Q0Origin where
  Q0Inferred : Q0Origin
  Q0 : Q0Origin
  Q0Erased : Q0Origin

data Q1Origin where
  Q1Inferred : Q1Origin
  Q1 : Q1Origin
  Q1Linear : Q1Origin

data QωOrigin where
  QωInferred : QωOrigin
  Qω : QωOrigin
  QωPlenty : QωOrigin

data OriginRelevant where
  ORelInferred : OriginRelevant
  ORelRelevant : OriginRelevant

data OriginIrrelevant where
  OIrrInferred : OriginIrrelevant
  OIrrDot : OriginIrrelevant
  OIrrIrr : OriginIrrelevant
  OIrrIrrelevant : OriginIrrelevant

data OriginShapeIrrelevant where
  OShIrrInferred : OriginShapeIrrelevant
  OShIrrDotDot : OriginShapeIrrelevant
  OShIrrShIrr : OriginShapeIrrelevant
  OShIrrShapeIrrelevant : OriginShapeIrrelevant

data Access where
  PrivateAccess : Origin → Access
  PublicAccess : Access

data IsInstance where
  InstanceDef : IsInstance
  NotInstanceDef : IsInstance

data Induction where
  Inductive : Induction
  CoInductive : Induction

data HasEta A where
  YesEta : HasEta A
  NoEta : A → HasEta A

data Catchall where
  YesCatchall : Catchall
  NoCatchall : Catchall

data TerminationCheck A where
  TerminationCheck′ : TerminationCheck A
  NoTerminationCheck : TerminationCheck A
  NonTerminating : TerminationCheck A
  Terminating : TerminationCheck A
  TerminationMeasure : A → TerminationCheck A

data Occurrence where
  Mixed : Occurrence
  JustNeg : Occurrence
  JustPos : Occurrence
  StrictPos : Occurrence
  GuardPos : Occurrence
  Unused : Occurrence

data List1 A where
  _∷¹_ : A → List A → List1 A

data List2 A where
  List2′ : A → A → List A → List2 A

