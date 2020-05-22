package thts;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.BitSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Queue;

import acceptance.AcceptanceOmega;
import acceptance.AcceptanceType;
import automata.DA;
import explicit.LTLModelChecker;
import explicit.MDP;
import explicit.MDPModelChecker;
import explicit.ProbModelChecker;
import parser.State;
import parser.ast.Expression;
import parser.ast.ExpressionProb;
import parser.ast.ExpressionQuant;
import parser.ast.ExpressionReward;
import parser.ast.ModulesFile;
import parser.ast.PropertiesFile;
import prism.ModelGenerator;
import prism.ModelInfo;
import prism.Prism;
import prism.PrismException;
import prism.PrismFileLog;
import prism.PrismLog;
import prism.ProductModelGenerator;
import prism.RewardGenerator;
import simulator.ModulesFileModelGenerator;

//just test whatever I want here 
public class TestThings {
	private String testsLocation;
	private String resultsLocation;

	public static void main(String[] args) {
		try {
			new TestThings().run();
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

	public void run() throws FileNotFoundException, PrismException {
		npprodmodgen();
	}

	public void npprodmodgen() throws PrismException, FileNotFoundException {
		AcceptanceType[] allowedAcceptance = { AcceptanceType.RABIN, AcceptanceType.REACH };
		System.out.println(System.getProperty("user.dir"));
		String currentDir = System.getProperty("user.dir");

		String dir = currentDir + "/prism-api/tests/wkspace/tro_examples/";// "/home/fatma/Data/PhD/code/prism_ws/prism-svn/prism/tests/wkspace/simpleTests/";
		// System.getProperty("user.dir");

		testsLocation = currentDir + "/prism-api/tests/wkspace/tro_examples/";

		resultsLocation = testsLocation + "/results/";
		String example = "tro_example_new_small";

		String saveplace = testsLocation;
		String filename = example;

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
		String alternatepropfn = saveplace + filename + ".prop";
		DA<BitSet, ? extends AcceptanceOmega> da = null;
		String modelFileName = filenames.get(0);
		String propertiesFileName = alternatepropfn;

		ModulesFile modulesFile = prism.parseModelFile(new File(modelFileName));
		prism.loadPRISMModel(modulesFile);

		PropertiesFile propertiesFile = prism.parsePropertiesFile(modulesFile, new File(propertiesFileName));

		LTLModelChecker ltlMC = new LTLModelChecker(prism);

		ModulesFileModelGenerator prismModelGen = new ModulesFileModelGenerator(modulesFile, prism);

		ModelGenerator modelGen = prismModelGen;
		ModelInfo modelInfo = modulesFile;

		prism.buildModel();
		MDP mdp = (MDP) prism.getBuiltModelExplicit();

		MDPModelChecker mc = new MDPModelChecker(prism);

		mc.setGenStrat(true);
		mc.setExportAdv(true);

		// now we've got to load all the properties
		// then we create a da for each property
		// if its a safety property we set a flag
		// and then we go on
		PropertiesFile altPropertiesFile = propertiesFile;// prism.parsePropertiesFile(modulesFile, new
															// File(alternatepropfile));

		mc.setModelCheckingInfo(modelInfo, altPropertiesFile, (RewardGenerator) prismModelGen);
		// so lets find out how many properties there are
		MDP oldproduct = null;

		ExpressionReward rewExpr = null;
		Expression safetyExpr = null;
		ArrayList<Expression> otherExpressions = new ArrayList<Expression>();
		// assumption a safety expression can not be a reward expression

		List<Expression> processedExprs = new ArrayList<Expression>();
		for (int i = 0; i < altPropertiesFile.getNumProperties(); i++) {
			System.out.println(altPropertiesFile.getProperty(i));
			// so reward + safety
			boolean isSafeExpr = false;
			Expression exprHere = altPropertiesFile.getProperty(i);
			if (exprHere instanceof ExpressionReward)
				rewExpr = (ExpressionReward) exprHere;
			else {
				Expression daExpr = ((ExpressionQuant) exprHere).getExpression();
				 isSafeExpr = !Expression.isCoSafeLTLSyntactic(daExpr, true);
				if (isSafeExpr)
					safetyExpr = daExpr;
				else
					otherExpressions.add(exprHere);
			}
			if (!isSafeExpr)
			processedExprs.add(((ExpressionQuant) exprHere).getExpression());
		}

		otherExpressions.add(((ExpressionQuant) rewExpr).getExpression());
		otherExpressions.add(safetyExpr);

		ProbModelChecker pmc = new ProbModelChecker(prism);
		oldproduct = mdp;

		ArrayList<List<Expression>> labelExprsList = new ArrayList<List<Expression>>();
		ArrayList<DA<BitSet, ? extends AcceptanceOmega>> das = new ArrayList<DA<BitSet, ? extends AcceptanceOmega>>();

		for (int i = 0; i < processedExprs.size(); i++) {
			List<Expression> labelExprs = new ArrayList<Expression>();

			Expression expr = (Expression) processedExprs.get(i);
			da = ltlMC.constructExpressionDAForLTLFormula(expr, labelExprs, allowedAcceptance);
			da.setDistancesToAcc();
			BitSet daAccStates = da.getAccStates();
			PrismLog out = new PrismFileLog(resultsLocation + "da_" + i + ".dot");
			// printing the da
			da.print(out, "dot");
			out.close();
			labelExprsList.add(labelExprs);
			das.add(da);
		}
		//lastly the safety expr 
		Expression expr = Expression.Not(safetyExpr); 
		List<Expression> labelExprs = new ArrayList<Expression>();
		da = ltlMC.constructExpressionDAForLTLFormula(expr, labelExprs, allowedAcceptance);
		da.setDistancesToAcc();
		BitSet daAccStates = da.getAccStates();
		PrismLog out = new PrismFileLog(resultsLocation + "da_safety.dot");
		// printing the da
		da.print(out, "dot");
		out.close();
		labelExprsList.add(labelExprs);
		das.add(da);
		
		NestedProductModelGenerator nppgen = new NestedProductModelGenerator(prismModelGen, das, labelExprsList);
		//so we get the initial state 
		//but possibly lets do this the right way 
		//so we want no not the safety da 
		List<State> initStates = nppgen.getInitialStates();
		Queue<State> q = new LinkedList<State>();
		q.addAll(initStates);
		while(!q.isEmpty())
		{
			State s = q.poll(); 
			System.out.println(s);
		}
//		prodModelGen = new ProductModelGenerator(prismModelGen, da, labelExprs);
//		prism.loadModelGenerator(prismModelGen);

	}

}
