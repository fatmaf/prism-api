package thts;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map.Entry;
import java.util.Vector;

import acceptance.AcceptanceOmega;
import acceptance.AcceptanceType;
import automata.DA;
import explicit.MDP;
import explicit.Model;
import explicit.ProbModelChecker;
import explicit.Product;
import explicit.LTLModelChecker;
import explicit.LTLModelChecker.LTLProduct;
import explicit.rewards.MDPRewardsSimple;
import parser.State;
import parser.ast.Expression;
import parser.ast.ExpressionQuant;
import prism.PrismException;
import prism.PrismFileLog;
import prism.PrismLog;

public class NestedProductMDP extends Product<MDP> {
	// so we'll keep track of all the DAs
	// so like each da and its index
	HashMap<Expression, Integer> daMap = null;
	ArrayList<DA<BitSet, ? extends AcceptanceOmega>> das = null;
	ArrayList<Expression> exprs = null;
	Vector<HashMap<Integer, Integer>> productStateToDAStateMap = null; // maps prod state i to da state
	HashMap<Integer, Integer> productStateToOriginalModelStateMap = null; // maps prod state to mdp state
	Vector<BitSet> originalModelStateToProductMap = null;
	Vector<Vector<BitSet>> daStateToProductStateMap = null;

	int safetyDAInd = -1; 
	BitSet acc = null; 
	BitSet avoid = null; 
	
	public NestedProductMDP(MDP originalModel) {
		super(originalModel);
		// TODO Auto-generated constructor stub
	}
	public void constructProductModel(Expression exprHere, LTLModelChecker ltlMC, ProbModelChecker pmc,
			AcceptanceType[] allowedAcceptance, String resLoc) throws PrismException {
		constructProductModel(exprHere, ltlMC,  pmc,
				allowedAcceptance, resLoc,false) ;
	}
	public void constructProductModel(Expression exprHere, LTLModelChecker ltlMC, ProbModelChecker pmc,
			AcceptanceType[] allowedAcceptance, String resLoc,boolean safetyDA) throws PrismException {
		MDP oldproduct = null;
		if (getProductModel() == null)
			oldproduct = getOriginalModel();
		else
			oldproduct = getProductModel();

		if (daMap == null)
			daMap = new HashMap<Expression, Integer>();
		int daIndex = daMap.size();
		daMap.put(exprHere, daIndex);
		if (das == null)
			das = new ArrayList<DA<BitSet, ? extends AcceptanceOmega>>();

		if (productStateToDAStateMap == null)
			productStateToDAStateMap = new Vector<HashMap<Integer, Integer>>();
		if (productStateToOriginalModelStateMap == null)
			productStateToOriginalModelStateMap = new HashMap<Integer, Integer>();

		Expression daExpr = ((ExpressionQuant) exprHere).getExpression();
		Vector<BitSet> labelBS = new Vector<BitSet>();

		DA<BitSet, ? extends AcceptanceOmega> daHere;
		if (safetyDA)
		{
			safetyDAInd = daIndex; 
			daExpr = Expression.Not(daExpr);
			daHere = ltlMC.constructDAForLTLFormula(pmc, oldproduct, daExpr, labelBS,
						allowedAcceptance);
		}
		else
		{
			daHere = ltlMC.constructDAForLTLFormula(pmc, oldproduct, daExpr, labelBS,
					allowedAcceptance);
		}
		das.add(daHere);
		
		LTLProduct<MDP> product = ltlMC.constructProductModel(daHere, oldproduct, labelBS, null);
//		product.getAutomatonState(0);
		// now we do all the mapping and stuff
		if (originalModelStateToProductMap == null) {
			originalModelStateToProductMap = new Vector<BitSet>();
			for (int i = 0; i < originalModel.getNumStates(); i++) {
				originalModelStateToProductMap.add(new BitSet());
			}
		}
		if (daStateToProductStateMap == null)
			daStateToProductStateMap = new Vector<Vector<BitSet>>();
		Vector<BitSet> daStateBitSet = new Vector<BitSet>();
		for (int i = 0; i < daHere.size(); i++) {
			daStateBitSet.add(new BitSet());
		}
		daStateToProductStateMap.add(daStateBitSet);

		HashMap<Integer, Integer> productStateToOriginalModelStateMapTemp = new HashMap<Integer, Integer>();
		HashMap<Integer, Integer> productStateToCurrentAutomatonStateMap = new HashMap<Integer, Integer>();
		Vector<HashMap<Integer, Integer>> productStateToDAStateMapTemp = new Vector<HashMap<Integer, Integer>>();
		for (int productState = 0; productState < product.getProductModel().getNumStates(); productState++) {

			// for the previous model
			int modelState = product.getModelState(productState);
			int automatonState = product.getAutomatonState(productState);

			int baseModelState = -1;
			if (productStateToOriginalModelStateMap.containsKey(modelState)) {
				baseModelState = productStateToOriginalModelStateMap.get(modelState);
			} else {
				baseModelState = modelState;
			}
			productStateToOriginalModelStateMapTemp.put(productState, baseModelState);
			productStateToCurrentAutomatonStateMap.put(productState, automatonState);
			// productStateToDAStateMap
			// updating all the previous i's really
			for (int jthda = 0; jthda < productStateToDAStateMap.size(); jthda++) {
				if (productStateToDAStateMapTemp.size() <= jthda) {
					productStateToDAStateMapTemp.add(new HashMap<Integer, Integer>());
				}
				int productStateToJthAutomatonState = productStateToDAStateMap.get(jthda).get(modelState);
				productStateToDAStateMapTemp.get(jthda).put(productState, productStateToJthAutomatonState);
			}

		}
		productStateToDAStateMapTemp.add(productStateToCurrentAutomatonStateMap);
		productStateToOriginalModelStateMap = productStateToOriginalModelStateMapTemp;
		productStateToDAStateMap = productStateToDAStateMapTemp;
//		BitSet daHereAccStates = daHere.getAccStates();

		printDA(resLoc, exprHere, daHere);

		this.productModel = product.getProductModel();
		printProduct(resLoc);
		// lets just print everything else too
		PrismLog out = new PrismFileLog(resLoc + "_prodmiscs_" + (das.size() - 1) + ".txt");
		out.println(productStateToOriginalModelStateMap.toString());
		out.println(productStateToDAStateMap.toString());
		out.close();
	}

	public void createTargetStates() {
		//states that are accepting states for all the das except the safetyda ones 
		Vector<BitSet> daAccStates = new Vector<BitSet>();
		int numstates = productModel.getNumStates();
		Vector<BitSet> prodDAAccStates =  new Vector<BitSet>();
		for (DA<BitSet, ? extends AcceptanceOmega> da : das) {
			daAccStates.add(da.getAccStates());
			prodDAAccStates.add(new BitSet(numstates));
		}
		int[] automatonStates = new int[das.size()];
	
	
		for (int prodstate = 0; prodstate < numstates; prodstate++) {
			for (int danum = 0; danum < productStateToDAStateMap.size(); danum++) {
				automatonStates[danum] = productStateToDAStateMap.get(danum).get(prodstate);
				if (daAccStates.get(danum).get(automatonStates[danum])) {
					prodDAAccStates.get(danum).set(prodstate);
				}
			}
			
		}
		BitSet avoid = null; 
		BitSet target = null;
		for(int i = 0; i<das.size(); i++)
		{
			if(i!=this.safetyDAInd)
			{
				if(target == null)
				{
					target =(BitSet) prodDAAccStates.get(i).clone();
				}
				else
				{
					target.and(prodDAAccStates.get(i));
				}
			}
			else {
				avoid = (BitSet) prodDAAccStates.get(i).clone();
			}
		}
		this.avoid = avoid; 
		this.acc = target; 
	}
	public BitSet getRemainStates()
	{
		int numstates = productModel.getNumStates();
		BitSet remain = new BitSet(numstates);
		if (avoid!=null)
		{
			remain = (BitSet) avoid.clone();
		}
			remain.flip(0,numstates);
		return remain;
	}
	public MDPRewardsSimple createTaskRewards() {

		Vector<BitSet> daAccStates = new Vector<BitSet>();
		for (DA<BitSet, ? extends AcceptanceOmega> da : das) {
			daAccStates.add(da.getAccStates());
		}
		int numstates = productModel.getNumStates();
		MDPRewardsSimple currentRewards = new MDPRewardsSimple(numstates);
		int[] automatonStates = new int[das.size()];
		int[] automatonStatesSucc = new int[das.size()];

		for (int prodstate = 0; prodstate < numstates; prodstate++) {
			for (int danum = 0; danum < productStateToDAStateMap.size(); danum++) {
				automatonStates[danum] = productStateToDAStateMap.get(danum).get(prodstate);
			}
			// so we use the nested da and create task rewards
			// for each state in the product we get the next state, if its an acc state
			// we check if they're not both acc states for the same da
			// and if they aren't we add a rew of p*1
			int numchoices = productModel.getNumChoices(prodstate);
			for (int prodstatechoice = 0; prodstatechoice < numchoices; prodstatechoice++) {
				Iterator<Entry<Integer, Double>> tranIter = productModel.getTransitionsIterator(prodstate, prodstatechoice);
				double allrew = 0;
				while (tranIter.hasNext()) {
					double rew = 0;
					Entry<Integer, Double> sp = tranIter.next();
					int ns = sp.getKey();
					double prob = sp.getValue();
					for (int danum = 0; danum < productStateToDAStateMap.size(); danum++) {
						automatonStatesSucc[danum] = productStateToDAStateMap.get(danum).get(ns);
						if (automatonStates[danum] != automatonStatesSucc[danum]) {
							if (daAccStates.get(danum).get(automatonStatesSucc[danum])) {
								rew += 1; // not the same //an accepting state
							}
						}
					}
					allrew += rew * prob;
				}
				currentRewards.addToTransitionReward(prodstate, prodstatechoice, allrew);
			}
		}
		return currentRewards;
	}

	public MDPRewardsSimple mapRewardsToCurrentProduct(MDPRewardsSimple costsModel) {
		// so now we just create a new rewards
		int numstates = productModel.getNumStates();
		MDPRewardsSimple currentRewards = new MDPRewardsSimple(numstates);

		double rew;
		for (int i = 0; i < numstates; i++) {
			int modelState = productStateToOriginalModelStateMap.get(i);
			rew = costsModel.getStateReward(modelState);
			currentRewards.addToStateReward(i, rew);
			// for each transition
			for (int j = 0; j < productModel.getNumChoices(i); j++) {
				rew = 0;
				// assuming unique actions in the mdp model for each state
				Object action = productModel.getAction(i, j);
				// find the corresponding action from the mdp

				int mdpactionindex = findActionIndexInOriginalModel(action, modelState);
				if (mdpactionindex != -1)
					rew = costsModel.getTransitionReward(modelState, mdpactionindex);
				currentRewards.addToTransitionReward(i, j, rew);

			}
		}
		return currentRewards;
	}

	public int findActionIndexInOriginalModel(Object action, int s) {
		int actionIndex = -1;
		int numc = originalModel.getNumChoices(s);
		for (int i = 0; i < numc; i++) {
			Object mdpAction = originalModel.getAction(s, i);
			if (action == null) {
				if (mdpAction == null) {
					actionIndex = i;
					break;
				}
			} else {
				if (mdpAction == null) {
					continue;
				} else if (action.toString().contentEquals(mdpAction.toString())) {
					actionIndex = i;
					break;
				}
			}

		}
		return actionIndex;
	}

	public void printDA(String resLoc, Expression exprHere, DA<BitSet, ? extends AcceptanceOmega> daHere)
			throws PrismException {
		PrismLog out = new PrismFileLog(resLoc + "_" + exprHere.toString() + ".dot");
		// printing the da

		daHere.print(out, "dot");
		out.close();
	}

	public void printProduct(String resLoc) throws PrismException {
		PrismLog out = new PrismFileLog(resLoc + "_npProd_" + (das.size() - 1) + ".dot");
		productModel.exportToDotFile(out, null, true);
		out.close();
	}

	public int getModelState(int productState) {
		return 0;
	}

	public State getNestedAutomatonState(int productState) {
		return null; // now this returns the automaton state
		// as a whole (x,x,x,x)
	}

	public int getAutomatonState(int productState, int automatonIndex) {
		return 0; // this returns a particular automatons state
	}

	public int getAutomatonIndex(Expression expr) {
		return daMap.get(expr); // this returns the index for that automaton
	}

	public BitSet liftFromAutomaton(BitSet automataStates, int automatonIndex) {
		BitSet result = new BitSet();
		for (int productState = 0; productState < productModel.getNumStates(); productState++) {
			if (automataStates.get(getAutomatonState(productState, automatonIndex))) {
				result.set(productState, true);
			}
		}
		return result;
	}

	@Override
	public int getAutomatonState(int productState) {
		// TODO Auto-generated method stub
		return 0;
	}

}
