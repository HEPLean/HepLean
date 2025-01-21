import HepLean.AnomalyCancellation.Basic
import HepLean.AnomalyCancellation.GroupActions
import HepLean.AnomalyCancellation.MSSMNu.B3
import HepLean.AnomalyCancellation.MSSMNu.Basic
import HepLean.AnomalyCancellation.MSSMNu.HyperCharge
import HepLean.AnomalyCancellation.MSSMNu.LineY3B3
import HepLean.AnomalyCancellation.MSSMNu.OrthogY3B3.Basic
import HepLean.AnomalyCancellation.MSSMNu.OrthogY3B3.PlaneWithY3B3
import HepLean.AnomalyCancellation.MSSMNu.OrthogY3B3.ToSols
import HepLean.AnomalyCancellation.MSSMNu.Permutations
import HepLean.AnomalyCancellation.MSSMNu.Y3
import HepLean.AnomalyCancellation.PureU1.Basic
import HepLean.AnomalyCancellation.PureU1.BasisLinear
import HepLean.AnomalyCancellation.PureU1.ConstAbs
import HepLean.AnomalyCancellation.PureU1.Even.BasisLinear
import HepLean.AnomalyCancellation.PureU1.Even.LineInCubic
import HepLean.AnomalyCancellation.PureU1.Even.Parameterization
import HepLean.AnomalyCancellation.PureU1.LineInPlaneCond
import HepLean.AnomalyCancellation.PureU1.LowDim.One
import HepLean.AnomalyCancellation.PureU1.LowDim.Three
import HepLean.AnomalyCancellation.PureU1.LowDim.Two
import HepLean.AnomalyCancellation.PureU1.Odd.BasisLinear
import HepLean.AnomalyCancellation.PureU1.Odd.LineInCubic
import HepLean.AnomalyCancellation.PureU1.Odd.Parameterization
import HepLean.AnomalyCancellation.PureU1.Permutations
import HepLean.AnomalyCancellation.PureU1.Sorts
import HepLean.AnomalyCancellation.PureU1.VectorLike
import HepLean.AnomalyCancellation.SM.Basic
import HepLean.AnomalyCancellation.SM.FamilyMaps
import HepLean.AnomalyCancellation.SM.NoGrav.Basic
import HepLean.AnomalyCancellation.SM.NoGrav.One.Lemmas
import HepLean.AnomalyCancellation.SM.NoGrav.One.LinearParameterization
import HepLean.AnomalyCancellation.SM.Permutations
import HepLean.AnomalyCancellation.SMNu.Basic
import HepLean.AnomalyCancellation.SMNu.FamilyMaps
import HepLean.AnomalyCancellation.SMNu.NoGrav.Basic
import HepLean.AnomalyCancellation.SMNu.Ordinary.Basic
import HepLean.AnomalyCancellation.SMNu.Ordinary.DimSevenPlane
import HepLean.AnomalyCancellation.SMNu.Ordinary.FamilyMaps
import HepLean.AnomalyCancellation.SMNu.Permutations
import HepLean.AnomalyCancellation.SMNu.PlusU1.BMinusL
import HepLean.AnomalyCancellation.SMNu.PlusU1.Basic
import HepLean.AnomalyCancellation.SMNu.PlusU1.BoundPlaneDim
import HepLean.AnomalyCancellation.SMNu.PlusU1.FamilyMaps
import HepLean.AnomalyCancellation.SMNu.PlusU1.HyperCharge
import HepLean.AnomalyCancellation.SMNu.PlusU1.PlaneNonSols
import HepLean.AnomalyCancellation.SMNu.PlusU1.QuadSol
import HepLean.AnomalyCancellation.SMNu.PlusU1.QuadSolToSol
import HepLean.BeyondTheStandardModel.GeorgiGlashow.Basic
import HepLean.BeyondTheStandardModel.PatiSalam.Basic
import HepLean.BeyondTheStandardModel.Spin10.Basic
import HepLean.BeyondTheStandardModel.TwoHDM.Basic
import HepLean.BeyondTheStandardModel.TwoHDM.GaugeOrbits
import HepLean.FlavorPhysics.CKMMatrix.Basic
import HepLean.FlavorPhysics.CKMMatrix.Invariants
import HepLean.FlavorPhysics.CKMMatrix.PhaseFreedom
import HepLean.FlavorPhysics.CKMMatrix.Relations
import HepLean.FlavorPhysics.CKMMatrix.Rows
import HepLean.FlavorPhysics.CKMMatrix.StandardParameterization.Basic
import HepLean.FlavorPhysics.CKMMatrix.StandardParameterization.StandardParameters
import HepLean.Lorentz.Algebra.Basic
import HepLean.Lorentz.Algebra.Basis
import HepLean.Lorentz.ComplexTensor.Basic
import HepLean.Lorentz.ComplexTensor.Basis
import HepLean.Lorentz.ComplexTensor.Bispinors.Basic
import HepLean.Lorentz.ComplexTensor.Lemmas
import HepLean.Lorentz.ComplexTensor.Metrics.Basic
import HepLean.Lorentz.ComplexTensor.Metrics.Basis
import HepLean.Lorentz.ComplexTensor.Metrics.Lemmas
import HepLean.Lorentz.ComplexTensor.PauliMatrices.Basic
import HepLean.Lorentz.ComplexTensor.PauliMatrices.Basis
import HepLean.Lorentz.ComplexTensor.PauliMatrices.CoContractContr
import HepLean.Lorentz.ComplexTensor.Units.Basic
import HepLean.Lorentz.ComplexTensor.Units.Symm
import HepLean.Lorentz.ComplexVector.Basic
import HepLean.Lorentz.ComplexVector.Contraction
import HepLean.Lorentz.ComplexVector.Metric
import HepLean.Lorentz.ComplexVector.Modules
import HepLean.Lorentz.ComplexVector.Two
import HepLean.Lorentz.ComplexVector.Unit
import HepLean.Lorentz.Group.Basic
import HepLean.Lorentz.Group.Boosts
import HepLean.Lorentz.Group.Orthochronous
import HepLean.Lorentz.Group.Proper
import HepLean.Lorentz.Group.Restricted
import HepLean.Lorentz.Group.Rotations
import HepLean.Lorentz.MinkowskiMatrix
import HepLean.Lorentz.PauliMatrices.AsTensor
import HepLean.Lorentz.PauliMatrices.Basic
import HepLean.Lorentz.PauliMatrices.SelfAdjoint
import HepLean.Lorentz.RealVector.Basic
import HepLean.Lorentz.RealVector.Contraction
import HepLean.Lorentz.RealVector.Modules
import HepLean.Lorentz.RealVector.NormOne
import HepLean.Lorentz.SL2C.Basic
import HepLean.Lorentz.SL2C.SelfAdjoint
import HepLean.Lorentz.Weyl.Basic
import HepLean.Lorentz.Weyl.Contraction
import HepLean.Lorentz.Weyl.Metric
import HepLean.Lorentz.Weyl.Modules
import HepLean.Lorentz.Weyl.Two
import HepLean.Lorentz.Weyl.Unit
import HepLean.Mathematics.Fin
import HepLean.Mathematics.Fin.Involutions
import HepLean.Mathematics.LinearMaps
import HepLean.Mathematics.List
import HepLean.Mathematics.List.InsertIdx
import HepLean.Mathematics.List.InsertionSort
import HepLean.Mathematics.PiTensorProduct
import HepLean.Mathematics.SO3.Basic
import HepLean.Mathematics.SchurTriangulation
import HepLean.Meta.AllFilePaths
import HepLean.Meta.Basic
import HepLean.Meta.Informal.Basic
import HepLean.Meta.Informal.Post
import HepLean.Meta.Notes.Basic
import HepLean.Meta.Notes.HTMLNote
import HepLean.Meta.Notes.NoteFile
import HepLean.Meta.Notes.ToHTML
import HepLean.Meta.TransverseTactics
import HepLean.PerturbationTheory.Algebras.CrAnAlgebra.Basic
import HepLean.PerturbationTheory.Algebras.CrAnAlgebra.NormalOrder
import HepLean.PerturbationTheory.Algebras.CrAnAlgebra.SuperCommute
import HepLean.PerturbationTheory.Algebras.OperatorAlgebra.Basic
import HepLean.PerturbationTheory.Algebras.OperatorAlgebra.NormalOrder
import HepLean.PerturbationTheory.Algebras.OperatorAlgebra.TimeContraction
import HepLean.PerturbationTheory.Algebras.StateAlgebra.Basic
import HepLean.PerturbationTheory.Algebras.StateAlgebra.TimeOrder
import HepLean.PerturbationTheory.CreateAnnihilate
import HepLean.PerturbationTheory.FeynmanDiagrams.Basic
import HepLean.PerturbationTheory.FeynmanDiagrams.Instances.ComplexScalar
import HepLean.PerturbationTheory.FeynmanDiagrams.Instances.Phi4
import HepLean.PerturbationTheory.FeynmanDiagrams.Momentum
import HepLean.PerturbationTheory.FieldSpecification.Basic
import HepLean.PerturbationTheory.FieldSpecification.CrAnSection
import HepLean.PerturbationTheory.FieldSpecification.CreateAnnihilate
import HepLean.PerturbationTheory.FieldSpecification.Examples
import HepLean.PerturbationTheory.FieldSpecification.Filters
import HepLean.PerturbationTheory.FieldSpecification.NormalOrder
import HepLean.PerturbationTheory.FieldSpecification.TimeOrder
import HepLean.PerturbationTheory.FieldStatistics.Basic
import HepLean.PerturbationTheory.FieldStatistics.ExchangeSign
import HepLean.PerturbationTheory.FieldStatistics.OfFinset
import HepLean.PerturbationTheory.Koszul.KoszulSign
import HepLean.PerturbationTheory.Koszul.KoszulSignInsert
import HepLean.PerturbationTheory.WickContraction.Basic
import HepLean.PerturbationTheory.WickContraction.Erase
import HepLean.PerturbationTheory.WickContraction.ExtractEquiv
import HepLean.PerturbationTheory.WickContraction.Insert
import HepLean.PerturbationTheory.WickContraction.InsertList
import HepLean.PerturbationTheory.WickContraction.Involutions
import HepLean.PerturbationTheory.WickContraction.IsFull
import HepLean.PerturbationTheory.WickContraction.Sign
import HepLean.PerturbationTheory.WickContraction.TimeContract
import HepLean.PerturbationTheory.WickContraction.Uncontracted
import HepLean.PerturbationTheory.WickContraction.UncontractedList
import HepLean.PerturbationTheory.WicksTheorem
import HepLean.SpaceTime.Basic
import HepLean.SpaceTime.CliffordAlgebra
import HepLean.StandardModel.Basic
import HepLean.StandardModel.HiggsBoson.Basic
import HepLean.StandardModel.HiggsBoson.GaugeAction
import HepLean.StandardModel.HiggsBoson.PointwiseInnerProd
import HepLean.StandardModel.HiggsBoson.Potential
import HepLean.StandardModel.Representations
import HepLean.Tensors.OverColor.Basic
import HepLean.Tensors.OverColor.Discrete
import HepLean.Tensors.OverColor.Functors
import HepLean.Tensors.OverColor.Iso
import HepLean.Tensors.OverColor.Lift
import HepLean.Tensors.TensorSpecies.Basic
import HepLean.Tensors.TensorSpecies.Contractions.Basic
import HepLean.Tensors.TensorSpecies.Contractions.Categorical
import HepLean.Tensors.TensorSpecies.Contractions.ContrMap
import HepLean.Tensors.TensorSpecies.DualRepIso
import HepLean.Tensors.TensorSpecies.MetricTensor
import HepLean.Tensors.TensorSpecies.Pure
import HepLean.Tensors.TensorSpecies.UnitTensor
import HepLean.Tensors.Tree.Basic
import HepLean.Tensors.Tree.Dot
import HepLean.Tensors.Tree.Elab
import HepLean.Tensors.Tree.NodeIdentities.Assoc
import HepLean.Tensors.Tree.NodeIdentities.Basic
import HepLean.Tensors.Tree.NodeIdentities.Congr
import HepLean.Tensors.Tree.NodeIdentities.ContrContr
import HepLean.Tensors.Tree.NodeIdentities.ContrSwap
import HepLean.Tensors.Tree.NodeIdentities.PermContr
import HepLean.Tensors.Tree.NodeIdentities.PermProd
import HepLean.Tensors.Tree.NodeIdentities.ProdAssoc
import HepLean.Tensors.Tree.NodeIdentities.ProdComm
import HepLean.Tensors.Tree.NodeIdentities.ProdContr
