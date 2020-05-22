package thts;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.List;

import acceptance.AcceptanceOmega;
import acceptance.AcceptanceReach;
import automata.DA;
import parser.State;
import parser.Values;
import parser.VarList;
import parser.ast.Declaration;
import parser.ast.DeclarationInt;
import parser.ast.Expression;
import parser.ast.RewardStruct;
import parser.type.Type;
import parser.type.TypeInt;
import prism.ModelGenerator;
import prism.ModelType;
import prism.PrismException;
import prism.PrismLangException;
import prism.RewardGenerator;
import simulator.ModulesFileModelGenerator;

public class NestedProductModelGenerator implements ModelGenerator, RewardGenerator {

	protected ModulesFileModelGenerator modelGen = null;
	/** The list of DAs used to build the product */
	protected ArrayList<DA<BitSet, ? extends AcceptanceOmega>> das = null;
	/** The expressions for the labels (APs) in the DAs */
	protected ArrayList<List<Expression>> labelExprs = null;
	/** Variable names for DAs states */
	protected ArrayList<String> daVars;
	/** Number of APs in the DAs */
	protected ArrayList<Integer> numAPs;
	/** Number of variables (num model vars + num das) */
	protected int numVars;
	/** Variable names */
	protected List<String> varNames;
	/** Variable types */
	protected List<Type> varTypes;
	/** Name for new acceptance label */
	protected String accLabel;
	/** Label names */
	protected List<String> labelNames;

	/** BitSet */
	protected ArrayList<BitSet> bsLabels;

	/** State to be explored in product */
	protected State exploreState;
	/** The model part of exploreState */
	protected State exploreModelState;
	/** The DA part of exploreState */
	protected ArrayList<Integer> exploreDaState;

	protected int numModelVars;
	protected int numDAs;

	public NestedProductModelGenerator(ModulesFileModelGenerator modelGen,
			ArrayList<DA<BitSet, ? extends AcceptanceOmega>> das, ArrayList<List<Expression>> labelExprs) {

		this.modelGen = modelGen;
		this.das = das;
		this.labelExprs = labelExprs;

		// so we have a list of das
		// each has a number and an index
		int numDAs = das.size();
		// find the beginning of the da variable
		// just incase we've been passed a model with a da
		int daStartNumber = 0;
		String expectedDAVar = "_da" + daStartNumber;
		while (modelGen.getVarIndex(expectedDAVar) != -1) {
			daStartNumber = daStartNumber + 1;
			expectedDAVar = "_da" + daStartNumber;
		}
		daVars = new ArrayList<String>();
		numAPs = new ArrayList<Integer>();
		varNames = new ArrayList<>();
		varNames.addAll(modelGen.getVarNames());
		varTypes = new ArrayList<>();
		varTypes.addAll(modelGen.getVarTypes());
		bsLabels = new ArrayList<BitSet>();
		// so our davars are the same size as numdas
		for (int d = 0; d < das.size(); d++) {
			expectedDAVar = "_da" + (daStartNumber + d);
			daVars.add(expectedDAVar);
			numAPs.add(das.get(d).getAPList().size());
			varNames.add(expectedDAVar);
			varTypes.add(TypeInt.getInstance());
			bsLabels.add(new BitSet(numAPs.get(d)));

		}
		accLabel = "_acc";
		labelNames = new ArrayList<String>(modelGen.getLabelNames());
		labelNames.add(accLabel);
		numVars = varNames.size();
		numModelVars = modelGen.getNumVars();
		numDAs = das.size();

	}
	// Accessors

	public List<String> getDAVarNames() {
		return daVars;
	}

	public String getDAVarName(int numda) {
		if (numda < numDAs)
			return daVars.get(numda);
		else
			return null;
	}

	// fatma added this
	// cuz I couldnt figure out how to get the label expressions otherwise
	// and I need them
	public int getNumLabelExprs(int numda) {
		return this.labelExprs.get(numda).size();
	}

	/**
	 * Assuming the product is build with a reach acceptance, is the state currently
	 * being explored a goal state?
	 */
	public boolean isReachAcceptanceGoalState(int numda) {
		DA<BitSet, ? extends AcceptanceOmega> da = das.get(numda);
		AcceptanceOmega acc = da.getAcceptance();
		if (!(acc instanceof AcceptanceReach)) {
			return false;
		}
		AcceptanceReach accReach = (AcceptanceReach) acc;
		return accReach.getGoalStates().get(exploreDaState.get(numda));
	}

	public boolean isReachAcceptanceGoalState(State state, int numda) {
		DA<BitSet, ? extends AcceptanceOmega> da = das.get(numda);
		AcceptanceOmega acc = da.getAcceptance();
		if (!(acc instanceof AcceptanceReach)) {
			return false;
		}
		AcceptanceReach accReach = (AcceptanceReach) acc;
		return accReach.getGoalStates().get(((Integer) state.varValues[numModelVars + numda]).intValue());
	}

	// Methods to implement ModelGenerator

	@Override
	public void setSomeUndefinedConstants(Values someValues) throws PrismException {
		modelGen.setSomeUndefinedConstants(someValues);
	}

	@Override
	public ModelType getModelType() {
		// TODO Auto-generated method stub
		return modelGen.getModelType();
	}

	@Override
	public List<String> getVarNames() {
		// TODO Auto-generated method stub
		return varNames;
	}

	@Override
	public List<Type> getVarTypes() {
		// TODO Auto-generated method stub
		return varTypes;
	}

	@Override
	public VarList createVarList() throws PrismException {
		// TODO Auto-generated method stub
		VarList varListModel = modelGen.createVarList();
		VarList varList = (VarList) varListModel.clone();
		// NB: if DA only has one state, we add an extra dummy state
		for (int i = 0; i < daVars.size(); i++) {
			String daVar = daVars.get(i);
			Declaration decl = new Declaration(daVar,
					new DeclarationInt(Expression.Int(0), Expression.Int(Math.max(das.get(i).size() - 1, 1))));
			try {
				varList.addVar(decl, 1, null);
			} catch (PrismLangException e) {
				// Shouldn't happen
				return null;
			}
		}
		return varList;
	}

	/**
	 * Find the successor of state {@code q} in the DA, taking the edge whose
	 * labelling matches the state {@code s}.
	 */
	protected int getDASuccessor(int danum, int q, State s) throws PrismException {
		DA<BitSet, ? extends AcceptanceOmega> da = das.get(danum);
		BitSet bsLabelsda = bsLabels.get(danum);
		List<Expression> labelExprsda = labelExprs.get(danum);
		// Create BitSet representing APs (labels) satisfied by state s
		for (int k = 0; k < numAPs.get(danum); k++) {
			bsLabelsda.set(k,
					labelExprsda.get(Integer.parseInt(da.getAPList().get(k).substring(1))).evaluateBoolean(s));
		}
		// Find/return successor
		return da.getEdgeDestByLabel(q, bsLabelsda);
	}

	public State createCombinedDAState(State sInit, boolean daInitStates) throws PrismException {
		State combinedDAState = new State(das.size());
		for (int d = 0; d < das.size(); d++) {
			int daStateHere;
			if (daInitStates)
				daStateHere = das.get(d).getStartState();
			else
				daStateHere = exploreDaState.get(d);
			int daInitState = getDASuccessor(d, daStateHere, sInit);
			combinedDAState.setValue(d, daInitState);
		}
		return new State(sInit, combinedDAState);
	}

	@Override
	public List<State> getInitialStates() throws PrismException {
		List<State> initStates = new ArrayList<>();

		for (State sInit : modelGen.getInitialStates()) {
			// automaton init states

			initStates.add(createCombinedDAState(sInit, true));
		}
		return initStates;
	}

	@Override
	public State getInitialState() throws PrismException {
		State sInit = modelGen.getInitialState();

		return createCombinedDAState(sInit, true);
	}

	@Override
	public void exploreState(State exploreState) throws PrismException {
		// TODO Auto-generated method stub
		this.exploreState = exploreState;
		exploreModelState = exploreState.substate(0, numModelVars);
		modelGen.exploreState(exploreModelState);
		if (exploreDaState == null)
			exploreDaState = new ArrayList<Integer>();
		for (int d = 0; d < das.size(); d++) {
			int daState = ((Integer) exploreState.varValues[numModelVars + d]).intValue();

			if (exploreDaState.size() <= d)
				exploreDaState.add(daState);
			else
				exploreDaState.set(d, daState);
			// exploreDaState = exploreState.substate(numVars -das.size(),numVars);
		}
		// ((Integer) exploreState.varValues[numVars - 1]).intValue();
	}

	@Override
	public int getNumChoices() throws PrismException {
		// TODO Auto-generated method stub
		return modelGen.getNumChoices();
	}

	@Override
	public int getNumTransitions(int i) throws PrismException {
		// TODO Auto-generated method stub
		return modelGen.getNumTransitions(i);
	}

	@Override
	public double getTransitionProbability(int i, int offset) throws PrismException {
		// TODO Auto-generated method stub
		return modelGen.getTransitionProbability(i, offset);
	}

	@Override
	public State computeTransitionTarget(int i, int offset) throws PrismException {
		// TODO Auto-generated method stub
		State sTarget = modelGen.computeTransitionTarget(i, offset);
		return createCombinedDAState(sTarget, false);
//		return new State(sTarget, new State(1).setValue(0, getDASuccessor(exploreDaState, sTarget)));

	}

	@Override
	public Object getTransitionAction(int i, int offset) throws PrismException {
		// TODO Auto-generated method stub
		return modelGen.getTransitionAction(i, offset);
	}
	// TODO FIX THIS FUNCTION!!!
	@Override
	public boolean isLabelTrue(String label) throws PrismException {
		System.out.println("ACC");
		if (accLabel.equalsIgnoreCase(label)) {
			return isReachAcceptanceGoalState(0); // TODO non acceptance
		} else {
			return modelGen.isLabelTrue(label);
		}
	}

	// TODO FIX THIS FUNCTION!!!
	@Override
	public boolean isLabelTrue(int i) throws PrismException {
		if (i == modelGen.getNumLabels()) {
			return isReachAcceptanceGoalState(0); // TODO non acceptance
		} else {
			return modelGen.isLabelTrue(i);
		}
	}

	// TODO FIX THIS FUNCTION!!!
	public double getProgressionRew(State source, State target) {

		DA<BitSet, ? extends AcceptanceOmega> da = das.get(0);
		int daSource = (int) source.varValues[numModelVars];
		int daTarget = (int) target.varValues[numModelVars];
		double prog = 100 * (da.getDistsToAcc().get(daSource) - da.getDistsToAcc().get(daTarget));
		// if (prog < 0.0) System.out.println(prog);
		// return Math.max(prog, 0);
		return prog;
	}

	// TODO FIX THIS FUNCTION!!!
	public double getDaDistanceCost(State state) {
		DA<BitSet, ? extends AcceptanceOmega> da = das.get(0);
		int daVal = (int) state.varValues[numModelVars];
		double res = da.getDistsToAcc().get(daVal);
		return res;
	}
	/*
	 * Added to check if an expression is true for a state islabel true didnt work
	 * here fatma
	 */
	// TODO FIX THIS FUNCTION!!!

	public boolean isExprTrue(int exprNum) throws PrismLangException {
		Expression expr = this.labelExprs.get(0).get(exprNum);
		return expr.evaluateBoolean(this.exploreState);
	}

	@Override
	public int getVarIndex(String name) {
		return varNames.indexOf(name);
	}

	@Override
	public String getVarName(int i) {
		return varNames.get(i);
	}

	@Override
	public int getNumLabels() {
		return labelNames.size();
	}

	@Override
	public List<String> getLabelNames() {
		return labelNames;
	}

	@Override
	public int getLabelIndex(String name) {
		return getLabelNames().indexOf(name);
	}

	@Override
	public String getLabelName(int i) throws PrismException {
		try {
			return getLabelNames().get(i);
		} catch (IndexOutOfBoundsException e) {
			throw new PrismException("Label number \"" + i + "\" not defined");
		}
	}

	@Override
	public int getNumRewardStructs() {
		return modelGen.getNumRewardStructs();
	}

	@Override
	public List<String> getRewardStructNames() {
		return modelGen.getRewardStructNames();
	}

	@Override
	public int getRewardStructIndex(String name) {
		return modelGen.getRewardStructIndex(name);
	}

	@Override
	public RewardStruct getRewardStruct(int i) throws PrismException {
		return modelGen.getRewardStruct(i);
	}

	@Override
	public boolean rewardStructHasTransitionRewards(int i) {
		return modelGen.rewardStructHasTransitionRewards(i);
	}

}
