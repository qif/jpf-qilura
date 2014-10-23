package uk.ac.qmul.sif;

import gov.nasa.jpf.Config;
import gov.nasa.jpf.JPF;
import gov.nasa.jpf.PropertyListenerAdapter;
import gov.nasa.jpf.jvm.bytecode.ARETURN;
import gov.nasa.jpf.jvm.bytecode.DRETURN;
import gov.nasa.jpf.jvm.bytecode.FRETURN;
import gov.nasa.jpf.jvm.bytecode.IRETURN;
import gov.nasa.jpf.jvm.bytecode.JVMInvokeInstruction;
import gov.nasa.jpf.jvm.bytecode.LRETURN;
import gov.nasa.jpf.search.Search;
import gov.nasa.jpf.symbc.bytecode.BytecodeUtils;
import gov.nasa.jpf.symbc.bytecode.INVOKESTATIC;
import gov.nasa.jpf.symbc.numeric.Expression;
import gov.nasa.jpf.symbc.numeric.IntegerConstant;
import gov.nasa.jpf.symbc.numeric.IntegerExpression;
import gov.nasa.jpf.symbc.numeric.PCChoiceGenerator;
import gov.nasa.jpf.symbc.numeric.PathCondition;
import gov.nasa.jpf.symbc.numeric.RealConstant;
import gov.nasa.jpf.symbc.numeric.RealExpression;
import gov.nasa.jpf.symbc.numeric.SymbolicInteger;
import gov.nasa.jpf.util.Pair;
import gov.nasa.jpf.vm.ChoiceGenerator;
import gov.nasa.jpf.vm.ClassInfo;
import gov.nasa.jpf.vm.Instruction;
import gov.nasa.jpf.vm.LocalVarInfo;
import gov.nasa.jpf.vm.MethodInfo;
import gov.nasa.jpf.vm.StackFrame;
import gov.nasa.jpf.vm.SystemState;
import gov.nasa.jpf.vm.ThreadInfo;
import gov.nasa.jpf.vm.Types;
import gov.nasa.jpf.vm.VM;
import gov.nasa.jpf.vm.bytecode.InvokeInstruction;
import gov.nasa.jpf.vm.bytecode.ReturnInstruction;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.Map;
import java.util.Vector;

import qs.phan.z3.Z3Converter;
import qs.phan.z3.Z3Visitor;

import com.microsoft.z3.ArithExpr;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Goal;
import com.microsoft.z3.Model;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import com.microsoft.z3.Z3Exception;

/*
 * Detecting information leaks by self-composition
 */
public class SelfCompListener extends PropertyListenerAdapter 
						// implements PublisherExtension 
{
	/*
	 * Locals to preserve the value that was held by JPF prior to changing it in
	 * order to turn off state matching during symbolic execution
	 */
	protected boolean retainVal = false;
	protected boolean forcedVal = false;

	protected Map<String, MethodSummary> allSummaries;
	protected ArrayList<SymbolicPath> lstOfPaths;
	// TODO: merge the setOfSymVals and lstOfSymVals
	protected Hashtable<String,Expr> setOfSymVals;
	protected String[] lstOfSymVals;
	//
	protected String[] secureMask;

	protected static final int SECURE = 0;
	protected static final int INSECURE = 1;
	protected static final int UNDECIDABLE = 2;

	Config conf;
	Context ctx;

	public SelfCompListener(Config config, JPF jpf) {
		allSummaries = new HashMap<String, MethodSummary>();
		lstOfPaths = new ArrayList<SymbolicPath>();
		setOfSymVals = new Hashtable<String,Expr>();
		conf = config;
		// get the security mask
		String method = conf.getProperty("secure.method");
		int s = method.indexOf('(');
		int e = method.indexOf(')');
		secureMask = method.substring(s + 1, e).split("#");
		HashMap<String, String> cfg = new HashMap<String, String>();
		cfg.put("model", "true");
		try{
			ctx = new Context(cfg);
		}
		catch(Z3Exception ex){
			ex.printStackTrace();
		}
	}

	public void instructionExecuted(VM vm, ThreadInfo currentThread, Instruction nextInstruction, Instruction executedInstruction) {

		if (!vm.getSystemState().isIgnored()) {
			Instruction insn = executedInstruction;
			SystemState ss = vm.getSystemState();
			ThreadInfo ti = currentThread;
			Config conf = vm.getConfig();

			if (insn instanceof InvokeInstruction) {
				JVMInvokeInstruction md = (JVMInvokeInstruction) insn;
				String methodName = md.getInvokedMethodName();
				int numberOfArgs = md.getArgumentValues(ti).length;

				MethodInfo mi = md.getInvokedMethod();
				ClassInfo ci = mi.getClassInfo();
				String className = ci.getName();

				StackFrame sf = ti.getTopFrame();
				String shortName = methodName;
				String longName = mi.getLongName();
				if (methodName.contains("("))
					shortName = methodName
							.substring(0, methodName.indexOf("("));
				// TODO: does not work for recursive invocations of sym methods;
				// should compare MethodInfo instead
				if (!shortName.equals(sf.getMethodName()))
					return;

				if ((BytecodeUtils.isClassSymbolic(conf, className, mi,
						methodName))
						|| BytecodeUtils.isMethodSymbolic(conf,
								mi.getFullName(), numberOfArgs, null)) {

					retainVal = ss.getRetainAttributes();
					forcedVal = ss.isForced();
					// turn off state matching
					ss.setForced(true);
					// make sure it stays turned off when a new state is created
					ss.retainAttributes(true);

					MethodSummary methodSummary = new MethodSummary();

					methodSummary.setMethodName(shortName);
					Object[] argValues = md.getArgumentValues(ti);
					String argValuesStr = "";
					for (int i = 0; i < argValues.length; i++) {
						argValuesStr = argValuesStr + argValues[i];
						if ((i + 1) < argValues.length)
							argValuesStr = argValuesStr + ",";
					}
					methodSummary.setArgValues(argValuesStr);
					byte[] argTypes = mi.getArgumentTypes();
					String argTypesStr = "";
					for (int i = 0; i < argTypes.length; i++) {
						argTypesStr = argTypesStr + argTypes[i];
						if ((i + 1) < argTypes.length)
							argTypesStr = argTypesStr + ",";
					}
					methodSummary.setArgTypes(argTypesStr);

					// get the symbolic values (changed from constructing them
					// here)
					String symValuesStr = "";
					String symVarNameStr = "";

					// String[] names = mi.getLocalVariableNames(); // seems
					// names does contain "this" so we need one more index :(
					// namesIndex
					LocalVarInfo[] argsInfo = mi.getArgumentLocalVars();

					if (argsInfo == null)
						throw new RuntimeException(
								"ERROR: you need to turn debug option on");

					int sfIndex = 1; // do not consider implicit param "this"
					int namesIndex = 1;
					if (md instanceof INVOKESTATIC) {
						sfIndex = 0; // no "this" for static
						namesIndex = 0;
					}

					for (int i = 0; i < numberOfArgs; i++) {
						Expression expLocal = (Expression) sf
								.getLocalAttr(sfIndex);
						if (expLocal != null) // symbolic
							symVarNameStr = expLocal.toString();
						else
							symVarNameStr = argsInfo[namesIndex].getName()
									+ "_CONCRETE" + ",";
						// symVarNameStr = "CONCRETE" + ",";
						symValuesStr = symValuesStr + symVarNameStr + ",";
						sfIndex++;
						namesIndex++;
						if (argTypes[i] == Types.T_LONG
								|| argTypes[i] == Types.T_DOUBLE)
							sfIndex++;

					}

					// get rid of last ","
					if (symValuesStr.endsWith(",")) {
						symValuesStr = symValuesStr.substring(0,
								symValuesStr.length() - 1);
					}
					methodSummary.setSymValues(symValuesStr);

					allSummaries.put(longName, methodSummary);
				}
			} else if (insn instanceof ReturnInstruction) {
				MethodInfo mi = insn.getMethodInfo();
				ClassInfo ci = mi.getClassInfo();
				if (null != ci) {
					String className = ci.getName();
					String methodName = mi.getName();
					String longName = mi.getLongName();
					int numberOfArgs = mi.getNumberOfArguments();

					if (((BytecodeUtils.isClassSymbolic(conf, className, mi,
							methodName)) || BytecodeUtils.isMethodSymbolic(
							conf, mi.getFullName(), numberOfArgs, null))) {

						ss.retainAttributes(retainVal);
						ss.setForced(forcedVal);
						ChoiceGenerator<?> cg = vm.getChoiceGenerator();
						if (!(cg instanceof PCChoiceGenerator)) {
							ChoiceGenerator<?> prev_cg = cg
									.getPreviousChoiceGenerator();
							while (!((prev_cg == null) || (prev_cg instanceof PCChoiceGenerator))) {
								prev_cg = prev_cg.getPreviousChoiceGenerator();
							}
							cg = prev_cg;
						}
						if ((cg instanceof PCChoiceGenerator)
								&& ((PCChoiceGenerator) cg).getCurrentPC() != null) {
							PathCondition pc = ((PCChoiceGenerator) cg)
									.getCurrentPC();

							pc.solve();

							String pcString = pc.stringPC();
							Pair<String, String> pcPair = null;
							// after the following statement is executed, the pc
							// loses its solution
							String returnString = "";

							Expression result = null;

							if (insn instanceof IRETURN) {
								IRETURN ireturn = (IRETURN) insn;
								int returnValue = ireturn.getReturnValue();
								IntegerExpression returnAttr = (IntegerExpression) ireturn
										.getReturnAttr(ti);
								if (returnAttr != null) {
									returnString = "Return Value: "
											+ String.valueOf(returnAttr
													.solution());
									result = returnAttr;
								} else { // concrete
									returnString = "Return Value: "
											+ String.valueOf(returnValue);
									result = new IntegerConstant(returnValue);
								}
							} else if (insn instanceof LRETURN) {
								LRETURN lreturn = (LRETURN) insn;
								long returnValue = lreturn.getReturnValue();
								IntegerExpression returnAttr = (IntegerExpression) lreturn
										.getReturnAttr(ti);
								if (returnAttr != null) {
									returnString = "Return Value: "
											+ String.valueOf(returnAttr
													.solution());
									result = returnAttr;
								} else { // concrete
									returnString = "Return Value: "
											+ String.valueOf(returnValue);
									result = new IntegerConstant(
											(int) returnValue);
								}
							} else if (insn instanceof DRETURN) {
								DRETURN dreturn = (DRETURN) insn;
								double returnValue = dreturn.getReturnValue();
								RealExpression returnAttr = (RealExpression) dreturn
										.getReturnAttr(ti);
								if (returnAttr != null) {
									returnString = "Return Value: "
											+ String.valueOf(returnAttr
													.solution());
									result = returnAttr;
								} else { // concrete
									returnString = "Return Value: "
											+ String.valueOf(returnValue);
									result = new RealConstant(returnValue);
								}
							} else if (insn instanceof FRETURN) {

								FRETURN freturn = (FRETURN) insn;
								double returnValue = freturn.getReturnValue();
								RealExpression returnAttr = (RealExpression) freturn
										.getReturnAttr(ti);
								if (returnAttr != null) {
									returnString = "Return Value: "
											+ String.valueOf(returnAttr
													.solution());
									result = returnAttr;
								} else { // concrete
									returnString = "Return Value: "
											+ String.valueOf(returnValue);
									result = new RealConstant(returnValue);
								}

							} else if (insn instanceof ARETURN) {
								ARETURN areturn = (ARETURN) insn;
								IntegerExpression returnAttr = (IntegerExpression) areturn
										.getReturnAttr(ti);
								if (returnAttr != null) {
									returnString = "Return Value: "
											+ String.valueOf(returnAttr
													.solution());
									result = returnAttr;
								} else {// concrete
									Object val = areturn.getReturnValue(ti);
									returnString = "Return Value: "
											+ String.valueOf(val);
									// DynamicElementInfo val =
									// (DynamicElementInfo)areturn.getReturnValue(ti);
									String tmp = String.valueOf(val);
									tmp = tmp
											.substring(tmp.lastIndexOf('.') + 1);
									result = new SymbolicInteger(tmp);

								}
							} else
								// other types of return
								returnString = "Return Value: --";

							pcString = pc.toString();
							pcPair = new Pair<String, String>(pcString,
									returnString);
							MethodSummary methodSummary = allSummaries
									.get(longName);
							Vector<Pair> pcs = methodSummary
									.getPathConditions();
							if ((!pcs.contains(pcPair))
									&& (pcString.contains("SYM"))) {
								methodSummary.addPathCondition(pcPair);
							}
							allSummaries.put(longName, methodSummary);

							if (result != null) {

								try {
									Z3Visitor visitor = new Z3Visitor(
											setOfSymVals, ctx);
									result.accept(visitor);

									Z3Converter converter = new Z3Converter(
											setOfSymVals, ctx);
									BoolExpr z3pc = converter.convertPC(pc);

									SymbolicPath sp = new SymbolicPath(z3pc,
													(ArithExpr) visitor.getExpression());
									lstOfPaths.add(sp);
								} catch (Z3Exception e) {
									e.printStackTrace();
								}
							}
						}
					}
				}
			}
		}
	}

	public void searchFinished(Search search) {

		Iterator it = allSummaries.entrySet().iterator();
		while (it.hasNext()) {
			Map.Entry me = (Map.Entry) it.next();
			MethodSummary methodSummary = (MethodSummary) me.getValue();
			lstOfSymVals = methodSummary.getSymValues().split(",");
			break;
		}
		
		verifyNonInterference();
	}

	private void verifyNonInterference() {

		if (optimiseNI() == UNDECIDABLE) // comment this line if do not use
											// optimisation
		{
			System.out.println(">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>");
			System.out.println("\nAnalyzing by z3...\n");
			try{
			if (isSelfCompValid())
				System.out.println("\nThe program is secure");
			else
				System.out.println("\nThe program violates non-interference\n");
			}
			catch(Z3Exception e){
				e.printStackTrace();
			}
			System.out.println("<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<");
		}
		
	}
	
	private boolean isSelfCompValid() throws Z3Exception{
		Expr[] high = new Expr[lstOfSymVals.length];
		Expr[] rename = new Expr[lstOfSymVals.length];
		int index = 0;
		for (int i = 0; i < lstOfSymVals.length; i++) {
			if (secureMask[i].equals("high")) {
				String name = lstOfSymVals[i];
				Expr val = setOfSymVals.get(name);
				high[index] = val;
				
				if(name.indexOf("_SYMINT") > -1){
					rename[index] = ctx.MkConst(ctx.MkSymbol("R_" + name), ctx.IntSort());
					index++;
				}
				if(name.indexOf("_SYMREAL") > -1){
					rename[index] = ctx.MkConst(ctx.MkSymbol("R_" + name), ctx.RealSort());
					index++;
				}
			}
		}
		
		BoolExpr selfcomp = ctx.MkFalse();
		for (int i = 0; i < lstOfPaths.size() - 1; i++) {
			for (int j = i + 1; j < lstOfPaths.size(); j++) {

				SymbolicPath spi = lstOfPaths.get(i);
				// second path is renamed
				SymbolicPath spj = lstOfPaths.get(j).rename(high,rename);

				BoolExpr path = ctx.MkAnd(new BoolExpr[]{ spi.getPathCondition(), spj.getPathCondition(), ctx.MkNot(ctx.MkEq(spi.getSymbolicOutput(), spj.getSymbolicOutput()))});
				selfcomp = ctx.MkOr(new BoolExpr[] {selfcomp, path});
			}
		}
		Goal goal = ctx.MkGoal(true, true, false);
		goal.Assert(selfcomp);
		
		//TODO: detect the logic from the symbolic variable
		Solver solver = ctx.MkSolver("QF_LIA");

        for (BoolExpr a : goal.Formulas())
            solver.Assert(a);

        // System.out.println(goal);
        
        if (solver.Check() == Status.SATISFIABLE){
        	Model m = solver.Model();
        	System.out.println("*******************************");
        	System.out.println("Model of self-composition is: ");
        	System.out.println(m);
        	System.out.println("*******************************");
        	ctx.Dispose();
        	return false;
        }
        ctx.Dispose();
		return true;
	}

	// implement the optimisation for non interference
	private int optimiseNI() {

		for (Iterator<SymbolicPath> i = lstOfPaths.iterator(); i.hasNext();) {
			SymbolicPath sp = (SymbolicPath) i.next();
			switch (sp.checkPath()) {
			case SymbolicPath.CLEAN_PATH:
				i.remove();
				break;
			case SymbolicPath.DIRECT_TAINT:
				System.out
						.println("The program leaks information via direct flow");
				return INSECURE;
			default:
				break;
			}

		}

		if (lstOfPaths.isEmpty()) {
			System.out.println("The program is secure");
			return SECURE;
		}

		return UNDECIDABLE;
	}
	
	protected class SymbolicPath {
		BoolExpr pc; // path condition
		ArithExpr so; // method summary

		int tag;

		public static final int CLEAN_PATH = 0;
		public static final int POSSIBLE_TAINT = 1;
		public static final int DIRECT_TAINT = 2;
		public static final int INDIRECT_TAINT = 3;

		public void taint() {
			if (tag == POSSIBLE_TAINT)
				tag = INDIRECT_TAINT;
		}

		public SymbolicPath(BoolExpr pathCondition, ArithExpr symbolicOutput) {
			pc = pathCondition;
			so = symbolicOutput;
			tag = CLEAN_PATH;
		}

		public SymbolicPath(BoolExpr pathCondition, ArithExpr symbolicOutput,
				int iTag) {
			pc = pathCondition;
			so = symbolicOutput;
			tag = iTag;
		}

		public BoolExpr getPathCondition() {
			return pc;
		}

		public ArithExpr getSymbolicOutput() {
			return so;
		}

		public SymbolicPath rename(Expr[] high, Expr[]rename) throws Z3Exception{
			BoolExpr pc1;
			ArithExpr so1;
			pc1 = (BoolExpr)pc.Substitute(high, rename);
			so1 = (ArithExpr)so.Substitute(high, rename);
			return new SymbolicPath(pc1, so1, tag);
		}

		public int getTag() {
			return tag;
		}

		public int checkPath() {
			
			for (int i = 0; i < lstOfSymVals.length; i++) {
				if (secureMask[i].equals("high")) {
					if (so.toString().contains(lstOfSymVals[i]))
						return tag = DIRECT_TAINT;
					else if (pc.toString().contains(lstOfSymVals[i]))
						return tag = POSSIBLE_TAINT;
				}
			}
			
			return tag;
		}
	}

	protected class MethodSummary {
		private String methodName = "";
		private String argTypes = "";
		private String argValues = "";
		private String symValues = "";
		private Vector<Pair> pathConditions;

		public MethodSummary() {
			pathConditions = new Vector<Pair>();
		}

		public void setMethodName(String mName) {
			this.methodName = mName;
		}

		public String getMethodName() {
			return this.methodName;
		}

		public void setArgTypes(String args) {
			this.argTypes = args;
		}

		public String getArgTypes() {
			return this.argTypes;
		}

		public void setArgValues(String vals) {
			this.argValues = vals;
		}

		public String getArgValues() {
			return this.argValues;
		}

		public void setSymValues(String sym) {
			this.symValues = sym;
		}

		public String getSymValues() {
			return this.symValues;
		}

		public void addPathCondition(Pair pc) {
			pathConditions.add(pc);
		}

		public Vector<Pair> getPathConditions() {
			return this.pathConditions;
		}

	}
}
