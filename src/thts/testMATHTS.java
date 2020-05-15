package thts;

import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashMap;
import java.util.Map.Entry;
import java.util.concurrent.TimeUnit;
import java.util.Stack;

import acceptance.AcceptanceOmega;
import automata.DA;
import thts.ResultsTiming.varIDs;
import parser.State;
import prism.Prism;
import prism.PrismException;
import prism.PrismFileLog;
import prism.PrismLog;

public class testMATHTS {

	String testsLocation = "/home/fatma/Data/PhD/code/prism_ws/prism-svn/prism/tests/decomp_tests/";

	String resultsLocation = "/home/fatma/Data/PhD/code/prism_ws/prism-svn/prism/tests/results/thts_res";

	public static void main(String[] args) {
		try {
			new testMATHTS().run();
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

	public void testTHTS(MultiAgentProductModelGenerator jpmg, PrismLog ml, String sv, String fn)
			throws PrismException {
		ArrayList<Objectives> tieBreakingOrder = new ArrayList<Objectives>();
		tieBreakingOrder.add(Objectives.Probability);
		tieBreakingOrder.add(Objectives.Progression);
		tieBreakingOrder.add(Objectives.Cost);
		ActionSelection actionSelection = new ActionSelectionGreedy(tieBreakingOrder);
		OutcomeSelection outcomeSelection = new OutcomeSelectionBoundsGreedy();
		HeuristicFunction heuristicFunction = new HeuristicFunctionPartSat(jpmg);
		BackupFunction backupFunction = new BackupFunctionFullBellman(jpmg, tieBreakingOrder);

		TrialBHeuristicSearch thts = new TrialBHeuristicSearch(ml, jpmg, actionSelection, outcomeSelection,
				heuristicFunction, backupFunction, tieBreakingOrder, sv, fn, null);
		Object a = thts.doTHTS("");
		ml.println(a.toString());
	}

	public void run() throws PrismException, IOException {
		String dir = "../prism/tests/wkspace/tro_examples/";//"/home/fatma/Data/PhD/code/prism_ws/prism-svn/prism/tests/wkspace/simpleTests/";
		// System.getProperty("user.dir");
	
		testsLocation = "../prism/tests/wkspace/tro_examples/";

		resultsLocation = testsLocation+"/results/";
		String example = "tro_example_new_small";
		testSingleAgentLoader(testsLocation,example,resultsLocation);


//		runGUISimpleTestsDebug1();

	}

	public void testMAPMG(PrismLog mainLog, ArrayList<SingleAgentLoader> sals, DA<BitSet, ? extends AcceptanceOmega> da,
			String saveplace, String fn) throws PrismException {
		boolean buildMDP = true;
		MultiAgentProductModelGenerator jpmg = new MultiAgentProductModelGenerator(mainLog, sals, da, buildMDP);
//		ArrayList<State> initStates = jpmg.createInitialStateFromRobotInitStates();
//		Stack<State> toVisit = new Stack<State>();
//		Stack<State> visited = new Stack<State>();
//		toVisit.addAll(initStates);
//		boolean checkhere = false; 
//		while(!toVisit.isEmpty())
//		{
//			State js = toVisit.pop();
//			visited.add(js);
//			//get the actions 
//			ArrayList<Object> jas = jpmg.getJointActions(js);
//			mainLog.println("Printing actions");
//			for(int i = 0; i<jas.size(); i++)
//			{
//				Object ja = jas.get(i);
//				mainLog.println(ja.toString()); 
//				if(ja.toString().contains("cd"))
//					checkhere = true; 
//				//get successors 
//				ArrayList<Entry<State, Double>> successors = jpmg.getSuccessors(js, ja);
//				for(int j = 0; j<successors.size(); j++)
//				{
//					State ss = successors.get(j).getKey();
//					if(!toVisit.contains(ss) && !visited.contains(ss))
//					{
//						toVisit.add(ss);
//					}
//					mainLog.println(successors.get(j).toString());
//				}
//			}
//		}
//		jpmg.saveBuiltMDP(saveplace, fn+"_all");
//		//now lets test the policy creator 
//		//and the random action selection thing 
//		ActionSelectionRandom randomActionSelector = new ActionSelectionRandom(jpmg.getBuiltMDP());
//		PolicyCreator pc = new PolicyCreator(); 
//		pc.createPolicy(jpmg.getBuiltMDP(), randomActionSelector); 
//		pc.savePolicy(saveplace, fn+"_random_policy");
		testTHTS(jpmg, mainLog, saveplace, fn);

	}

	public void testSingleAgentLoader(String saveplace,String filename,String TESTSLOC) throws PrismException, FileNotFoundException {

//		String saveplace = "/home/fatma/Data/PhD/code/prism_ws/prism-svn/prism/tests/decomp_tests/";
//		String filename = "tiny_example_permtrap";// "no_door_example";
//		String TESTSLOC = "/home/fatma/Data/PhD/code/prism_ws/prism-svn/prism/tests/results/";

		// Create a log for PRISM output (hidden or stdout)
		// PrismLog mainLog = new PrismDevNullLog();

		PrismLog mainLog = new PrismFileLog("stdout");
		Long startTime = System.currentTimeMillis();

		// Initialise PRISM engine

		Prism prism = new Prism(mainLog);
		prism.initialise();
		prism.setEngine(Prism.EXPLICIT);

		ArrayList<String> filenames = new ArrayList<String>();
//		filenames.add(saveplace+filename+".prism");
		filenames.add(saveplace + filename + "0.prism");
//		filenames.add(saveplace + filename + "1.prism");
		String propfilename = saveplace + filename + ".props";
		String alternatepropfn = saveplace+filename+".prop";
		DA<BitSet, ? extends AcceptanceOmega> da = null;
		ArrayList<SingleAgentLoader> sals = new ArrayList<SingleAgentLoader>();
		ArrayList<String> ssl = new ArrayList<String>();
//		ssl.add("door");
		ssl = null;
		for (int i = 0; i < filenames.size(); i++) {
			String modelName = filenames.get(i);
			SingleAgentLoader sal = new SingleAgentLoader(prism, mainLog, filename + i, modelName, propfilename,
					TESTSLOC, ssl);
			sal.setUp();
			
			sal.solutionProdModelVarListsAreSynced();
			da = sal.getSingleAgentModelGenReturnDA();
			sal.solutionProdModelVarListsAreSynced();
			sal.solveUsingVI();
			sal.solutionProdModelVarListsAreSynced();
			sal.solveUsingPartialSatisfaction();
			sal.solutionProdModelVarListsAreSynced();
			sal.solveUsingPartSatMaxTask(alternatepropfn);
			sal.cleanUp();
			State s = sal.prodModelGen.getInitialState();
			double d = sal.getSolutionValue(s, Objectives.Probability);
			d = sal.getSolutionValue(s, Objectives.Progression);
			d = sal.getSolutionValue(s, Objectives.Cost);
			boolean isdeadend = sal.isDeadend(s);
			sal.getDAState(s);
			sal.getDAStateAsInt(s);
			sal.getSharedState(s);
			sal.getPrivateState(s);
			mainLog.println(d);
			sals.add(sal);
			// not tested the create robot state function

		}
//		testMAPMG(mainLog, sals, da, TESTSLOC, filename);

	}

	public void doTHTS(String resLoc, String modelLoc, String filename, int numRobots, int numTasks, int numDoors,
			int numFS) throws PrismException, FileNotFoundException {

		// Create a log for PRISM output (hidden or stdout)
		// PrismLog mainLog = new PrismDevNullLog();

		PrismLog mainLog = new PrismFileLog("stdout");
		ResultsTiming resSaver = new ResultsTiming(mainLog, filename, resLoc, true);

		resSaver.recordInits(numRobots, "Robots", varIDs.numrobots);
		resSaver.recordInits(numTasks, "Tasks", varIDs.numtasks);
		resSaver.recordInits(numDoors, "Doors", varIDs.numdoors);
		resSaver.recordInits(numFS, "Failstates", varIDs.failstates);

		Long startTime = System.nanoTime();
		boolean buildMDP = false;
		// Initialise PRISM engine

		resSaver.setGlobalStartTime();
//		resSaver.setScopeStartTime();
		resSaver.setLocalStartTime();

		Prism prism = new Prism(mainLog);
		prism.initialise();
		prism.setEngine(Prism.EXPLICIT);

		ArrayList<String> filenames = new ArrayList<String>();
		for (int i = 0; i < numRobots; i++) {
			filenames.add(modelLoc + filename + i + ".prism");
//		filenames.add(testsLocation + filename + i+".prism");
		}
		String propfilename = modelLoc + filename + ".props";
		String alternatepropfn = modelLoc + filename + ".prop";
		DA<BitSet, ? extends AcceptanceOmega> da = null;
		ArrayList<SingleAgentLoader> sals = new ArrayList<SingleAgentLoader>();
		ArrayList<String> ssl = null;
		if (numDoors > 0) {
			ssl = new ArrayList<String>();
			for (int i = 0; i < numDoors; i++) {
				ssl.add("door" + i);
			}
		}


		for (int i = 0; i < filenames.size(); i++) {
			resSaver.setScopeStartTime();
			String modelName = filenames.get(i);
			SingleAgentLoader sal = new SingleAgentLoader(prism, mainLog, filename + i, modelName, propfilename,
					resLoc, ssl);

			sal.setUp();
			da = sal.getSingleAgentModelGenReturnDA();

			resSaver.recordTime("model loading time " + modelName, varIDs.modelloadingtimes, true);
			resSaver.setLocalStartTime();
			
			sal.solveUsingPartialSatisfaction();
			
			sal.solutionProdModelVarListsAreSynced();



			
			sal.cleanUp();

			int maxStateEstimate = sal.getMaxStatesEstimate();
			resSaver.recordTime("Single Agent Solution " + i, varIDs.singleagentsolutiontimes, true);
			resSaver.recordValues(maxStateEstimate, "Single Agent " + i + " States", varIDs.nestedproductstates);
			
			sals.add(sal);

			
		}
		resSaver.recordTime("all models loading time", varIDs.totalmodelloadingtime, false);
		resSaver.recordTime("Total Single Agent Solution Time", varIDs.allnestedproductcreationtime, false);

		resSaver.setScopeStartTime();
		long elapsedTime = System.nanoTime() - startTime;
		mainLog.println("Single Agent Models Loaded and Solved " + elapsedTime + "ns "
				+ TimeUnit.MILLISECONDS.convert(elapsedTime, TimeUnit.NANOSECONDS) + " ms "
				+ TimeUnit.SECONDS.convert(elapsedTime, TimeUnit.NANOSECONDS) + "s");

		MultiAgentProductModelGenerator jpmg = new MultiAgentProductModelGenerator(mainLog, sals, da, buildMDP);

		ArrayList<Objectives> tieBreakingOrder = new ArrayList<Objectives>();
		tieBreakingOrder.add(Objectives.Probability);
//		tieBreakingOrder.add(Objectives.Progression);
		tieBreakingOrder.add(Objectives.Cost);
		mainLog.println("Objectives:"); 
		for(Objectives obj : tieBreakingOrder)
			mainLog.println(obj.toString());
		ActionSelection actionSelection = 
		//		new ActionSelectionEpsilonGreedyInvertedBounds(tieBreakingOrder);
				new ActionSelectionGreedy(tieBreakingOrder);
		OutcomeSelection outcomeSelection = 
			//	new OutcomeSelectionBoundsSoftmax(jpmg.getMaxStatesEstimate());
				new OutcomeSelectionBoundsGreedy();
		HeuristicFunction heuristicFunction = new HeuristicFunctionPartSat(jpmg);
		BackupFunction backupFunction = new BackupFunctionFullBellman(jpmg, tieBreakingOrder);

		TrialBHeuristicSearch thts = new TrialBHeuristicSearch(mainLog, jpmg, actionSelection, outcomeSelection,
				heuristicFunction, backupFunction, tieBreakingOrder, resLoc, filename, resSaver);
		int mt = thts.setMaxTrialLength();
		resSaver.recordTime("Multi Agent Product Initialization", varIDs.jointmodelgentime, true);
		mainLog.println("Max Trial Length: " + mt);
		mainLog.println("Beginning THTS************************************************");
		Entry<Object, HashMap<String, Double>> res = thts.doTHTS(resSaver.gettrialName());
		mainLog.println("************************************************End THTS");
		Object a = res.getKey();
		resSaver.saveValues(res.getValue());
		if (a != null)
			mainLog.println(a.toString());

		elapsedTime = System.nanoTime() - startTime;
		mainLog.println(
				"Completed in " + elapsedTime + "ns " + TimeUnit.MILLISECONDS.convert(elapsedTime, TimeUnit.NANOSECONDS)
						+ " ms " + TimeUnit.SECONDS.convert(elapsedTime, TimeUnit.NANOSECONDS) + "s");
		resSaver.writeResults();
	}


	
	public void runGUISimpleTestsDebug1() throws IOException {
		// saving filenames etc
		String dir = "../prism/tests/wkspace/tro_examples/";//"/home/fatma/Data/PhD/code/prism_ws/prism-svn/prism/tests/wkspace/simpleTests/";
		// System.getProperty("user.dir");
	
		testsLocation = "../prism/tests/wkspace/tro_examples/";

		resultsLocation = testsLocation+"/results/";
		HashMap<String, Boolean> example_has_door_list = new HashMap<String, Boolean>();
		HashMap<String, Integer> example_num_door_list = new HashMap<String, Integer>();
		HashMap<String, Integer> example_num_robot_list = new HashMap<String, Integer>();
		HashMap<String, Integer> example_num_goals_list = new HashMap<String, Integer>();
		HashMap<String, Integer> example_num_fs_list = new HashMap<String, Integer>();
		ArrayList<String> examples = new ArrayList<String>();
		ArrayList<String> example_ids = new ArrayList<String>();

		int numRobots = 2;
		int numFS = 0;
		int numGoals = 3;
		int numDoors = 1;
		String example = "tro_example_new_small";
		
		String example_id = example;

		String example_to_run = example;
	
		example_id = example; 

		example_has_door_list.put(example_id, numDoors > 0);
		example_num_door_list.put(example_id, numDoors);
		example_num_robot_list.put(example_id, numRobots);
		example_num_fs_list.put(example_id, numFS);
		example_num_goals_list.put(example_id, numGoals);

		examples.add(example_id);
		example_ids.add(example);

		
		int maxGoals = 9;
		ArrayList<String> testsDone = new ArrayList<String>();
		int maxFiles = examples.size() * 3 * 4;
		int testCount = 0;
		try {
			for (int i = 0; i < examples.size(); i++) {
				example_to_run = examples.get(i);
				example_id = example_ids.get(i);

				int maxRobots = example_num_robot_list.get(example_id);
				maxGoals = example_num_goals_list.get(example_id)+1;
				int r = Math.min(2, maxRobots); int g = 2;{
					{
	//			for (int r = 2; r <= maxRobots; r += 2) {
//					for (int g = 2; g <= maxGoals; g += 2) {

						System.out.println(">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>" + example_id + " r" + r + " g" + g
								+ ">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>");
						System.out.println(">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>" + testCount + " of " + maxFiles + " : "
								+ ((double) (testCount + 1) / (double) maxFiles)
								+ ">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>");

//						doTHTS(dir + "results/thts", dir, example_to_run, r, g, example_num_door_list.get(example_id),
//								example_num_fs_list.get(example_id));

						testCount++;
						testsDone.add(example_id);
						System.out.println("<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<" + example_id + " r" + r + " g" + g
								+ "<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<");
					}
				}
			}

		} catch (Exception e) {
			System.out.println("Error: " + e.getMessage());
			System.exit(1);
		} 

		System.out.println("Num tests: " + testCount);
	}


	

	public void reWritePropsFileGUISimpleTests(String loc, String fn, int numGoals) throws IOException {

		HashMap<String, HashMap<Integer, String>> goalStrings = new HashMap<String, HashMap<Integer, String>>();
		HashMap<Integer, String> thisHashMap = new HashMap<Integer, String>();
		String f = "g5_r3_t3_d2_fs3";
		String gs = "Pmax=? [ (F (s=0) )& (F (s=2) )& (F (s=4) ) & (G ( ! (s=11) ) )  & (G ( ! (s=14) ) )  & (G ( ! (s=17) ) ) ]";
		thisHashMap.put(2, "Pmax=? [ (F (s=0) ) & (G ( ! (s=11) ) )  & (G ( ! (s=14) ) )  & (G ( ! (s=17) ) ) ]");
		thisHashMap.put(3,
				"Pmax=? [ (F (s=0) ) & (F (s=2) ) & (G ( ! (s=11) ) )  & (G ( ! (s=14) ) )  & (G ( ! (s=17) ) ) ]");
		thisHashMap.put(4,
				"Pmax=? [ (F (s=0) ) & (F (s=2) ) & (F (s=4) ) & (G ( ! (s=11) ) )  & (G ( ! (s=14) ) )  & (G ( ! (s=17) ) ) ]");

		goalStrings.put(f, thisHashMap);
		

//		g5_r3_t3_d0_fs0.props
//		Pmax=? [ (F (s=0) ) & (F (s=2) ) & (F (s=4) ) & (G ( ! (s=11) ) )  & (G ( ! (s=14) ) )  & (G ( ! (s=17) ) ) ]
		f = "g5_r3_t3_d0_fs0";
		thisHashMap = new HashMap<Integer, String>();
		thisHashMap.put(2, 
				"Pmax=? [ (F (s=0) )  & (G ( ! (s=11) ) )  & (G ( ! (s=14) ) )  & (G ( ! (s=17) ) ) ]");
		thisHashMap.put(3,
				"Pmax=? [ (F (s=0) ) & (F (s=2) ) & (G ( ! (s=11) ) )  & (G ( ! (s=14) ) )  & (G ( ! (s=17) ) ) ]");
		thisHashMap.put(4,
				"Pmax=? [ (F (s=0) ) & (F (s=2) ) & (F (s=4) ) & (G ( ! (s=11) ) )  & (G ( ! (s=14) ) )  & (G ( ! (s=17) ) ) ]");
		goalStrings.put(f, thisHashMap);

		//		g5_r3_t3_d0_fs3.props
//		Pmax=? [ (F (s=0) ) & (F (s=2) ) & (F (s=4) ) & (G ( ! (s=11) ) )  & (G ( ! (s=14) ) )  & (G ( ! (s=17) ) ) ]
		f = "g5_r3_t3_d0_fs3";
		thisHashMap = new HashMap<Integer, String>();
		thisHashMap.put(2, 
				"Pmax=? [ (F (s=0) ) & (G ( ! (s=11) ) )  & (G ( ! (s=14) ) )  & (G ( ! (s=17) ) ) ]");
		thisHashMap.put(3,
				"Pmax=? [ (F (s=0) ) & (F (s=2) ) & (G ( ! (s=11) ) )  & (G ( ! (s=14) ) )  & (G ( ! (s=17) ) ) ]");
		thisHashMap.put(4,
				"Pmax=? [ (F (s=0) ) & (F (s=2) ) & (F (s=4) ) & (G ( ! (s=11) ) )  & (G ( ! (s=14) ) )  & (G ( ! (s=17) ) ) ]");
		goalStrings.put(f, thisHashMap);

		//		g5_r3_t3_d2_fs3.props
//		Pmax=? [ (F (s=0) ) & (F (s=2) ) & (F (s=4) ) & (G ( ! (s=11) ) )  & (G ( ! (s=14) ) )  & (G ( ! (s=17) ) ) ]
		f = "g5_r3_t3_d2_fs3";
		thisHashMap = new HashMap<Integer, String>();
		thisHashMap.put(2, 
				"Pmax=? [ (F (s=0) )  & (G ( ! (s=11) ) )  & (G ( ! (s=14) ) )  & (G ( ! (s=17) ) ) ]");
		thisHashMap.put(3,
				"Pmax=? [ (F (s=0) ) & (F (s=2) ) & (G ( ! (s=11) ) )  & (G ( ! (s=14) ) )  & (G ( ! (s=17) ) ) ]");
		thisHashMap.put(4,
				"Pmax=? [ (F (s=0) ) & (F (s=2) ) & (F (s=4) ) & (G ( ! (s=11) ) )  & (G ( ! (s=14) ) )  & (G ( ! (s=17) ) ) ]");
		goalStrings.put(f, thisHashMap);

		//		g7_r5_t6_d0_fs1.props
//		Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) )& (F (s=27) )& (F (s=28) )& (F (s=30) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]
		f = "g7_r5_t6_d0_fs1";
		thisHashMap = new HashMap<Integer, String>();
		thisHashMap.put(2,
				"Pmax=? [ (F (s=0) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");

		thisHashMap.put(3,
				"Pmax=? [ (F (s=0) )& (F (s=4) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");
		thisHashMap.put(4,
				"Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");

		thisHashMap.put(5,
				"Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) )& (F (s=27) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");

		thisHashMap.put(6,
				"Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) )& (F (s=27) )& (F (s=28) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");

		thisHashMap.put(7,
				"Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) )& (F (s=27) )& (F (s=28) )& (F (s=30) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");
		goalStrings.put(f, thisHashMap);
		//		g7_r5_t6_d0_fs3.props
//		Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) )& (F (s=27) )& (F (s=28) )& (F (s=30) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]
		f = "g7_r5_t6_d0_fs3";
		thisHashMap = new HashMap<Integer, String>();
		thisHashMap.put(2,
				"Pmax=? [ (F (s=0) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");

		thisHashMap.put(3,
				"Pmax=? [ (F (s=0) )& (F (s=4) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");
		thisHashMap.put(4,
				"Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");

		thisHashMap.put(5,
				"Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) )& (F (s=27) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");

		thisHashMap.put(6,
				"Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) )& (F (s=27) )& (F (s=28) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");

		thisHashMap.put(7,
				"Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) )& (F (s=27) )& (F (s=28) )& (F (s=30) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");
		goalStrings.put(f, thisHashMap);

		//		g7_r5_t6_d0_fs5.props
//		Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) )& (F (s=27) )& (F (s=28) )& (F (s=30) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]
		f = "g7_r5_t6_d0_fs5";
		thisHashMap = new HashMap<Integer, String>();
		thisHashMap.put(2,
				"Pmax=? [ (F (s=0) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");

		thisHashMap.put(3,
				"Pmax=? [ (F (s=0) )& (F (s=4) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");
		thisHashMap.put(4,
				"Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");

		thisHashMap.put(5,
				"Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) )& (F (s=27) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");

		thisHashMap.put(6,
				"Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) )& (F (s=27) )& (F (s=28) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");

		thisHashMap.put(7,
				"Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) )& (F (s=27) )& (F (s=28) )& (F (s=30) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");
		goalStrings.put(f, thisHashMap);

		//		g7_r5_t6_d1_fs1.props
//		Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) )& (F (s=27) )& (F (s=28) )& (F (s=30) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]
		f = "g7_r5_t6_d1_fs1";
		thisHashMap = new HashMap<Integer, String>();
		thisHashMap.put(2,
				"Pmax=? [ (F (s=0) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");

		thisHashMap.put(3,
				"Pmax=? [ (F (s=0) )& (F (s=4) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");
		thisHashMap.put(4,
				"Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");

		thisHashMap.put(5,
				"Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) )& (F (s=27) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");

		thisHashMap.put(6,
				"Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) )& (F (s=27) )& (F (s=28) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");

		thisHashMap.put(7,
				"Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) )& (F (s=27) )& (F (s=28) )& (F (s=30) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");
		goalStrings.put(f, thisHashMap);

		//		g7_r5_t6_d2_fs1.props
//		Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) )& (F (s=27) )& (F (s=28) )& (F (s=30) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]
		f = "g7_r5_t6_d2_fs1";
		thisHashMap = new HashMap<Integer, String>();
		thisHashMap.put(2,
				"Pmax=? [ (F (s=0) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");

		thisHashMap.put(3,
				"Pmax=? [ (F (s=0) )& (F (s=4) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");
		thisHashMap.put(4,
				"Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");

		thisHashMap.put(5,
				"Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) )& (F (s=27) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");

		thisHashMap.put(6,
				"Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) )& (F (s=27) )& (F (s=28) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");

		thisHashMap.put(7,
				"Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) )& (F (s=27) )& (F (s=28) )& (F (s=30) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");
		goalStrings.put(f, thisHashMap);

		//		g7_r5_t6_d2_fs2.props
//		Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) )& (F (s=27) )& (F (s=28) )& (F (s=30) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]
		f = "g7_r5_t6_d2_fs2";
		thisHashMap = new HashMap<Integer, String>();
		thisHashMap.put(2,
				"Pmax=? [ (F (s=0) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");

		thisHashMap.put(3,
				"Pmax=? [ (F (s=0) )& (F (s=4) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");
		thisHashMap.put(4,
				"Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");

		thisHashMap.put(5,
				"Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) )& (F (s=27) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");

		thisHashMap.put(6,
				"Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) )& (F (s=27) )& (F (s=28) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");

		thisHashMap.put(7,
				"Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) )& (F (s=27) )& (F (s=28) )& (F (s=30) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");
		goalStrings.put(f, thisHashMap);

		//		g7_r5_t6_d2_fs3.props
//		Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) )& (F (s=27) )& (F (s=28) )& (F (s=30) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]
		f = "g7_r5_t6_d2_fs3";
		thisHashMap = new HashMap<Integer, String>();
		thisHashMap.put(2,
				"Pmax=? [ (F (s=0) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");

		thisHashMap.put(3,
				"Pmax=? [ (F (s=0) )& (F (s=4) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");
		thisHashMap.put(4,
				"Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");

		thisHashMap.put(5,
				"Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) )& (F (s=27) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");

		thisHashMap.put(6,
				"Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) )& (F (s=27) )& (F (s=28) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");

		thisHashMap.put(7,
				"Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) )& (F (s=27) )& (F (s=28) )& (F (s=30) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");
		goalStrings.put(f, thisHashMap);

		//		g7_r5_t6_d2_fs4.props
//		Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) )& (F (s=27) )& (F (s=28) )& (F (s=30) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]
		f = "g7_r5_t6_d2_fs4";
		thisHashMap = new HashMap<Integer, String>();
		thisHashMap.put(2,
				"Pmax=? [ (F (s=0) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");

		thisHashMap.put(3,
				"Pmax=? [ (F (s=0) )& (F (s=4) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");
		thisHashMap.put(4,
				"Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");

		thisHashMap.put(5,
				"Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) )& (F (s=27) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");

		thisHashMap.put(6,
				"Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) )& (F (s=27) )& (F (s=28) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");

		thisHashMap.put(7,
				"Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) )& (F (s=27) )& (F (s=28) )& (F (s=30) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");
		goalStrings.put(f, thisHashMap);

		//		g7_r5_t6_d3_fs1.props
//		Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) )& (F (s=27) )& (F (s=28) )& (F (s=30) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]
		f = "g7_r5_t6_d3_fs1";
		thisHashMap = new HashMap<Integer, String>();
		thisHashMap.put(2,
				"Pmax=? [ (F (s=0) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");

		thisHashMap.put(3,
				"Pmax=? [ (F (s=0) )& (F (s=4) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");
		thisHashMap.put(4,
				"Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");

		thisHashMap.put(5,
				"Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) )& (F (s=27) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");

		thisHashMap.put(6,
				"Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) )& (F (s=27) )& (F (s=28) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");

		thisHashMap.put(7,
				"Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) )& (F (s=27) )& (F (s=28) )& (F (s=30) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");
		goalStrings.put(f, thisHashMap);

		//		g7_r5_t6_d3_fs2.props
//		Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) )& (F (s=27) )& (F (s=28) )& (F (s=30) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]
		f = "g7_r5_t6_d3_fs2";
		thisHashMap = new HashMap<Integer, String>();
		thisHashMap.put(2,
				"Pmax=? [ (F (s=0) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");

		thisHashMap.put(3,
				"Pmax=? [ (F (s=0) )& (F (s=4) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");
		thisHashMap.put(4,
				"Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");

		thisHashMap.put(5,
				"Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) )& (F (s=27) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");

		thisHashMap.put(6,
				"Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) )& (F (s=27) )& (F (s=28) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");

		thisHashMap.put(7,
				"Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) )& (F (s=27) )& (F (s=28) )& (F (s=30) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");
		goalStrings.put(f, thisHashMap);

		//		g7_r5_t6_d3_fs3.props
//		Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) )& (F (s=27) )& (F (s=28) )& (F (s=30) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]
		f = "g7_r5_t6_d3_fs3";
		thisHashMap = new HashMap<Integer, String>();
		thisHashMap.put(2,
				"Pmax=? [ (F (s=0) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");

		thisHashMap.put(3,
				"Pmax=? [ (F (s=0) )& (F (s=4) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");
		thisHashMap.put(4,
				"Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");

		thisHashMap.put(5,
				"Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) )& (F (s=27) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");

		thisHashMap.put(6,
				"Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) )& (F (s=27) )& (F (s=28) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");

		thisHashMap.put(7,
				"Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) )& (F (s=27) )& (F (s=28) )& (F (s=30) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");
		goalStrings.put(f, thisHashMap);

		//		g7_r5_t6_d3_fs4.props
//		Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) )& (F (s=27) )& (F (s=28) )& (F (s=30) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]
		f = "g7_r5_t6_d3_fs4";
		thisHashMap = new HashMap<Integer, String>();
		thisHashMap.put(2,
				"Pmax=? [ (F (s=0) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");

		thisHashMap.put(3,
				"Pmax=? [ (F (s=0) )& (F (s=4) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");
		thisHashMap.put(4,
				"Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");

		thisHashMap.put(5,
				"Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) )& (F (s=27) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");

		thisHashMap.put(6,
				"Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) )& (F (s=27) )& (F (s=28) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");

		thisHashMap.put(7,
				"Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) )& (F (s=27) )& (F (s=28) )& (F (s=30) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");
		goalStrings.put(f, thisHashMap);

		//		g7_r5_t6_d4_fs1.props
//		Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) )& (F (s=27) )& (F (s=28) )& (F (s=30) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]
		f = "g7_r5_t6_d4_fs1";
		thisHashMap = new HashMap<Integer, String>();
		thisHashMap.put(2,
				"Pmax=? [ (F (s=0) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");

		thisHashMap.put(3,
				"Pmax=? [ (F (s=0) )& (F (s=4) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");
		thisHashMap.put(4,
				"Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");

		thisHashMap.put(5,
				"Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) )& (F (s=27) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");

		thisHashMap.put(6,
				"Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) )& (F (s=27) )& (F (s=28) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");

		thisHashMap.put(7,
				"Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) )& (F (s=27) )& (F (s=28) )& (F (s=30) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");
		goalStrings.put(f, thisHashMap);

		//		g7_r5_t6_d4_fs2.props
//		Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) )& (F (s=27) )& (F (s=28) )& (F (s=30) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]
		f = "g7_r5_t6_d4_fs2";
		thisHashMap = new HashMap<Integer, String>();
		thisHashMap.put(2,
				"Pmax=? [ (F (s=0) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");

		thisHashMap.put(3,
				"Pmax=? [ (F (s=0) )& (F (s=4) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");
		thisHashMap.put(4,
				"Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");

		thisHashMap.put(5,
				"Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) )& (F (s=27) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");

		thisHashMap.put(6,
				"Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) )& (F (s=27) )& (F (s=28) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");

		thisHashMap.put(7,
				"Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) )& (F (s=27) )& (F (s=28) )& (F (s=30) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");
		goalStrings.put(f, thisHashMap);

		//		g7_r5_t6_d4_fs3.props
//		Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) )& (F (s=27) )& (F (s=28) )& (F (s=30) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]
		f = "g7_r5_t6_d4_fs3";
		thisHashMap = new HashMap<Integer, String>();
		thisHashMap.put(2,
				"Pmax=? [ (F (s=0) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");

		thisHashMap.put(3,
				"Pmax=? [ (F (s=0) )& (F (s=4) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");
		thisHashMap.put(4,
				"Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");

		thisHashMap.put(5,
				"Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) )& (F (s=27) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");

		thisHashMap.put(6,
				"Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) )& (F (s=27) )& (F (s=28) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");

		thisHashMap.put(7,
				"Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) )& (F (s=27) )& (F (s=28) )& (F (s=30) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");
		goalStrings.put(f, thisHashMap);

		//		g7_r5_t6_d4_fs4.props
//		Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) )& (F (s=27) )& (F (s=28) )& (F (s=30) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]
		f = "g7_r5_t6_d4_fs4";
		thisHashMap = new HashMap<Integer, String>();
		thisHashMap.put(2,
				"Pmax=? [ (F (s=0) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");

		thisHashMap.put(3,
				"Pmax=? [ (F (s=0) )& (F (s=4) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");
		thisHashMap.put(4,
				"Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");

		thisHashMap.put(5,
				"Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) )& (F (s=27) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");

		thisHashMap.put(6,
				"Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) )& (F (s=27) )& (F (s=28) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");

		thisHashMap.put(7,
				"Pmax=? [ (F (s=0) )& (F (s=4) )& (F (s=6) )& (F (s=27) )& (F (s=28) )& (F (s=30) ) & (G ( ! (s=14) ) )  & (G ( ! (s=16) ) ) ]");
		goalStrings.put(f, thisHashMap);

		
		
		

		String goalString = goalStrings.get(fn).get(numGoals);

		System.out.println(goalString);

		FileWriter fileWriter = new FileWriter(loc + fn + ".props");
		PrintWriter printWriter = new PrintWriter(fileWriter);
		printWriter.print(goalString + "\n");

		printWriter.close();
	}

	public void reWritePropsFile(String fn, int numGoals) throws IOException {
		HashMap<Integer, String> goalStrings = new HashMap<Integer, String>();
		goalStrings.put(13,
				"Pmax=? [ (F (s=0) )& (F (s=2) )& (F (s=4) )& (F (s=6) )& (F (s=8) )& (F (s=10) )& (F (s=84) )& (F (s=85) )& (F (s=86) )& (F (s=87) )& (F (s=88) )& (F (s=89) ) & (G ( ! (s=19) ) )  & (G ( ! (s=23) ) )  & (G ( ! (s=25) ) )  & (G ( ! (s=29) ) )  & (G ( ! (s=31) ) )  & (G ( ! (s=35) ) )  & (G ( ! (s=59) ) )  & (G ( ! (s=60) ) )  & (G ( ! (s=65) ) )  & (G ( ! (s=66) ) ) ]");
		goalStrings.put(12,
				"Pmax=? [ (F (s=0) )& (F (s=2) )& (F (s=4) )& (F (s=6) )& (F (s=8) )& (F (s=10) )& (F (s=84) )& (F (s=85) )& (F (s=86) )& (F (s=87) )& (F (s=88) ) & (G ( ! (s=19) ) )  & (G ( ! (s=23) ) )  & (G ( ! (s=25) ) )  & (G ( ! (s=29) ) )  & (G ( ! (s=31) ) )  & (G ( ! (s=35) ) )  & (G ( ! (s=59) ) )  & (G ( ! (s=60) ) )  & (G ( ! (s=65) ) )  & (G ( ! (s=66) ) ) ]");
		goalStrings.put(11,
				"Pmax=? [ (F (s=0) )& (F (s=2) )& (F (s=4) )& (F (s=6) )& (F (s=8) )& (F (s=10) )& (F (s=84) )& (F (s=85) )& (F (s=86) )& (F (s=87) ) & (G ( ! (s=19) ) )  & (G ( ! (s=23) ) )  & (G ( ! (s=25) ) )  & (G ( ! (s=29) ) )  & (G ( ! (s=31) ) )  & (G ( ! (s=35) ) )  & (G ( ! (s=59) ) )  & (G ( ! (s=60) ) )  & (G ( ! (s=65) ) )  & (G ( ! (s=66) ) ) ]");
		goalStrings.put(10,
				"Pmax=? [ (F (s=0) )& (F (s=2) )& (F (s=4) )& (F (s=6) )& (F (s=8) )& (F (s=10) )& (F (s=84) )& (F (s=85) )& (F (s=86) ) & (G ( ! (s=19) ) )  & (G ( ! (s=23) ) )  & (G ( ! (s=25) ) )  & (G ( ! (s=29) ) )  & (G ( ! (s=31) ) )  & (G ( ! (s=35) ) )  & (G ( ! (s=59) ) )  & (G ( ! (s=60) ) )  & (G ( ! (s=65) ) )  & (G ( ! (s=66) ) ) ]");
		goalStrings.put(9,
				"Pmax=? [ (F (s=0) )& (F (s=2) )& (F (s=4) )& (F (s=6) )& (F (s=8) )& (F (s=10) )& (F (s=84) )& (F (s=85) ) & (G ( ! (s=19) ) )  & (G ( ! (s=23) ) )  & (G ( ! (s=25) ) )  & (G ( ! (s=29) ) )  & (G ( ! (s=31) ) )  & (G ( ! (s=35) ) )  & (G ( ! (s=59) ) )  & (G ( ! (s=60) ) )  & (G ( ! (s=65) ) )  & (G ( ! (s=66) ) ) ]");
		goalStrings.put(8,
				"Pmax=? [ (F (s=0) )& (F (s=2) )& (F (s=4) )& (F (s=6) )& (F (s=8) )& (F (s=10) )& (F (s=84) ) & (G ( ! (s=19) ) )  & (G ( ! (s=23) ) )  & (G ( ! (s=25) ) )  & (G ( ! (s=29) ) )  & (G ( ! (s=31) ) )  & (G ( ! (s=35) ) )  & (G ( ! (s=59) ) )  & (G ( ! (s=60) ) )  & (G ( ! (s=65) ) )  & (G ( ! (s=66) ) ) ]");
		goalStrings.put(7,
				"Pmax=? [ (F (s=0) )& (F (s=2) )& (F (s=4) )& (F (s=6) )& (F (s=8) )& (F (s=10) ) & (G ( ! (s=19) ) )  & (G ( ! (s=23) ) )  & (G ( ! (s=25) ) )  & (G ( ! (s=29) ) )  & (G ( ! (s=31) ) )  & (G ( ! (s=35) ) )  & (G ( ! (s=59) ) )  & (G ( ! (s=60) ) )  & (G ( ! (s=65) ) )  & (G ( ! (s=66) ) ) ]");
		goalStrings.put(6,
				"Pmax=? [ (F (s=0) )& (F (s=2) )& (F (s=4) )& (F (s=6) )& (F (s=8) ) & (G ( ! (s=19) ) )  & (G ( ! (s=23) ) )  & (G ( ! (s=25) ) )  & (G ( ! (s=29) ) )  & (G ( ! (s=31) ) )  & (G ( ! (s=35) ) )  & (G ( ! (s=59) ) )  & (G ( ! (s=60) ) )  & (G ( ! (s=65) ) )  & (G ( ! (s=66) ) ) ]");
		goalStrings.put(5,
				"Pmax=? [ (F (s=0) )& (F (s=2) )& (F (s=4) )& (F (s=6) ) & (G ( ! (s=19) ) )  & (G ( ! (s=23) ) )  & (G ( ! (s=25) ) )  & (G ( ! (s=29) ) )  & (G ( ! (s=31) ) )  & (G ( ! (s=35) ) )  & (G ( ! (s=59) ) )  & (G ( ! (s=60) ) )  & (G ( ! (s=65) ) )  & (G ( ! (s=66) ) ) ]");
		goalStrings.put(4,
				"Pmax=? [ (F (s=0) )& (F (s=2) )& (F (s=4) ) & (G ( ! (s=19) ) )  & (G ( ! (s=23) ) )  & (G ( ! (s=25) ) )  & (G ( ! (s=29) ) )  & (G ( ! (s=31) ) )  & (G ( ! (s=35) ) )  & (G ( ! (s=59) ) )  & (G ( ! (s=60) ) )  & (G ( ! (s=65) ) )  & (G ( ! (s=66) ) ) ]");
		goalStrings.put(3,
				"Pmax=? [ (F (s=0) )& (F (s=2) ) & (G ( ! (s=19) ) )  & (G ( ! (s=23) ) )  & (G ( ! (s=25) ) )  & (G ( ! (s=29) ) )  & (G ( ! (s=31) ) )  & (G ( ! (s=35) ) )  & (G ( ! (s=59) ) )  & (G ( ! (s=60) ) )  & (G ( ! (s=65) ) )  & (G ( ! (s=66) ) ) ]");
		goalStrings.put(2,
				"Pmax=? [ (F (s=0) ) & (G ( ! (s=19) ) )  & (G ( ! (s=23) ) )  & (G ( ! (s=25) ) )  & (G ( ! (s=29) ) )  & (G ( ! (s=31) ) )  & (G ( ! (s=35) ) )  & (G ( ! (s=59) ) )  & (G ( ! (s=60) ) )  & (G ( ! (s=65) ) )  & (G ( ! (s=66) ) ) ]");

		String goalString = goalStrings.get(numGoals);

		System.out.println(goalString);

		FileWriter fileWriter = new FileWriter(fn);
		PrintWriter printWriter = new PrintWriter(fileWriter);
		printWriter.print(goalString + "\n");

		printWriter.close();
	}
}
