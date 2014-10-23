package uk.ac.qmul.sif;

import gov.nasa.jpf.Config;
import gov.nasa.jpf.JPF;
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

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.io.Writer;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Vector;

import name.filieri.antonio.jpf.analysis.Analyzer;
import name.filieri.antonio.jpf.analysis.SequentialAnalyzer;
import name.filieri.antonio.jpf.domain.ProblemSetting;
import name.filieri.antonio.jpf.utils.BigRational;
import name.filieri.antonio.jpf.utils.Configuration;

import org.antlr.runtime.RecognitionException;
import org.apache.commons.io.FileUtils;

import qs.phan.smtlib2.SMTLIB2Converter;
import qs.phan.z3.Z3Converter;
import qs.phan.z3.Z3Visitor;

import com.microsoft.z3.ArithExpr;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Goal;
import com.microsoft.z3.Model;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import com.microsoft.z3.Z3Exception;

public class QiluraListener extends SelfCompListener
{
		private ArrayList<String> lstOfAntoPaths;
		// TODO: merge the setOfSymVals and lstOfSymVals
		private int N = 0;

		public QiluraListener(Config config, JPF jpf) {
			super(config,jpf);
			lstOfAntoPaths = new ArrayList<String>();
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
										// add Antonio's formatting PC
										String antoPath = SMTLIB2Converter.cleanExpr(pc.header.toString());
										
										/* Corina suggested to ask output constraints to PC, but it doesn't work
										if (sp.checkPath() == SymbolicPath.DIRECT_TAINT){
											antoPath = antoPath + " &&\n" + "O_1_SYMINT = " + PrefixConverter.cleanExpr(result.toString());
										}
										//*/	
											
										lstOfAntoPaths.add(antoPath);
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

			// printAllPaths();
			createUserProfile();
			
			quantify();
			
			// clean directory
			String tmpDir = conf.getProperty("symbolic.reliability.tmpDir");
			try {
				FileUtils.cleanDirectory(new File(tmpDir));
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			} 
			
		}

		private void createUserProfile(){
			StringBuilder sb = new StringBuilder();
			sb.append("domain{\n");
			int i; int count = 0;
			for (i = 0; i < lstOfSymVals.length; i++) {
				if (secureMask[i].equals("high")) {
					String name = lstOfSymVals[i];
					count++;
					sb.append("\t" + name +  " : 0,1000000;\n");
				}	
			}
			sb.append("};\n\n");
			sb.append("usageProfile{\n\t");
			int count2 = 0;
			for (i = 0; i < lstOfSymVals.length; i++) {
				if (secureMask[i].equals("high")) {
					String name = lstOfSymVals[i];
					sb.append(name + "==" + name);
					count2++;
					if (count2 < count)
						sb.append(" && ");
				}	
			}
			sb.append(" : 100/100;\n};");
			// write user profile to file
			String tmpDir = conf.getProperty("symbolic.reliability.tmpDir");
			String target = conf.getProperty("target");
			String upFile = tmpDir + "/" + target + ".up";
			Writer writer = null;

			try {
			    writer = new BufferedWriter(new OutputStreamWriter(
			          new FileOutputStream(upFile), "utf-8"));
			    writer.write(sb.toString());
			    conf.setProperty("symbolic.reliability.problemSettings",upFile);
			} catch (IOException ex) {
			  // report
			} finally {
			   try {writer.close();} catch (Exception ex) {}
			}
		}
		
		private void quantify() {

			try {
			labelPaths();
			}
			catch(Z3Exception e){
				e.printStackTrace();
			}
			
			HashSet<String> set = new HashSet<String>();
			for (int i = 0; i < lstOfPaths.size(); i++) {
				SymbolicPath spi = lstOfPaths.get(i);
				String pci = lstOfAntoPaths.get(i);
				switch (spi.getTag()) {
				case SymbolicPath.INDIRECT_TAINT:
					N++;
					break;
				case SymbolicPath.DIRECT_TAINT:
					set.add(pci);
					break;
				default:
					System.out.println(">>>Secure labeled " + spi.getTag());
				}
			}

			if (set.isEmpty()) { // program doesn't leak via direct flow
				if (N == 0)
					System.out.println("Program is secure");
				else
					// program leaks via implicit flow
					System.out.println("Maximum leakage is " + +Math.log(N)
							/ Math.log(2) + " bits");
				return;
			}
			// program leaks via direct flow:
			// leak = leak via implicit flow + leak via direct flow
			Configuration configuration = new Configuration();
			configuration.setTemporaryDirectory(conf
					.getProperty("symbolic.reliability.tmpDir"));
			configuration.setOmegaExectutablePath(this.conf
					.getProperty("symbolic.reliability.omegaPath"));
			configuration.setLatteExecutablePath(this.conf
					.getProperty("symbolic.reliability.lattePath"));

			ProblemSetting problemSettings = null;
			String problemSettingsPath = conf
					.getProperty("symbolic.reliability.problemSettings");
			if (problemSettingsPath == null) {
				throw new RuntimeException(
						"Problem settings must be dummy or privided by file.");
			}
			try {
				problemSettings = ProblemSetting.loadFromFile(problemSettingsPath);
				System.out.println("Problem settings loaded from: "
						+ problemSettingsPath);
			} catch (IOException e) {
				e.printStackTrace();
			} catch (RecognitionException e) {
				e.printStackTrace();
			}

			try {
				Analyzer analyzer = new SequentialAnalyzer(configuration,
						problemSettings.getDomain(),
						problemSettings.getUsageProfile(), 1);
				BigRational numberOfPoints = analyzer.countPointsOfSetOfPCs(set);
				System.out.println(">>>Leakage of information is: "
						+ Math.log(N + Integer.parseInt(numberOfPoints.toString()))
						/ Math.log(2) + " bits");
				analyzer.terminate();
			} catch (Exception e) {
				e.printStackTrace();
			}
		}

		protected void printAllPaths() {
			for (String sp : lstOfAntoPaths) {
				System.out.println("***********************************");
				System.out.println(sp);
				System.out.println("***********************************");
			}
		}
		
		private void labelPaths() throws Z3Exception {

			for (Iterator<SymbolicPath> i = lstOfPaths.iterator(); i.hasNext();) {
				SymbolicPath sp = (SymbolicPath) i.next();
				sp.checkPath();
			}
			
			int numHigh = 0;
			
			for(String mask: secureMask)
				if ("high".equals(mask)) numHigh++;
			
			Expr[] high = new Expr[numHigh];
			Expr[] rename = new Expr[numHigh];
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

			// System.out.println("There are " + lstOfPaths.size() + " symbolic paths");
			
			for (int i = 0; i < lstOfPaths.size() - 1; i++) {
				SymbolicPath spi = lstOfPaths.get(i);
				for (int j = i + 1; j < lstOfPaths.size(); j++) {
					SymbolicPath spj = lstOfPaths.get(j).rename(high,rename);

					int it = spi.getTag();
					int jt = spj.getTag();
					if ((it == SymbolicPath.POSSIBLE_TAINT || jt == SymbolicPath.POSSIBLE_TAINT)
							&& (it != SymbolicPath.CLEAN_PATH)
							&& (jt != SymbolicPath.CLEAN_PATH)) {
						try {
							BoolExpr pathEquivalence = ctx.MkAnd(new BoolExpr[]{ spi.getPathCondition(), spj.getPathCondition(), ctx.MkNot(ctx.MkEq(spi.getSymbolicOutput(), spj.getSymbolicOutput()))});
							// solve by z3
							Goal goal = ctx.MkGoal(true, true, false);
							goal.Assert(pathEquivalence);
							
							//TODO: detect the logic from the symbolic variable
							Solver solver = ctx.MkSolver("QF_LIA");

					        for (BoolExpr a : goal.Formulas())
					            solver.Assert(a);

					        // System.out.println(goal);
					        
					        if (solver.Check() == Status.SATISFIABLE){
					        	lstOfPaths.get(i).taint();
								lstOfPaths.get(j).taint();
								if(false) // TODO: edit later
								{
						        	Model m = solver.Model();
						        	System.out.println("*******************************");
						        	System.out.println("Model of pair [" + i + "," + j + "] is: ");
						        	System.out.println(m);
						        	System.out.println("*******************************");
								}
							}
						} catch (Exception e) {
							e.printStackTrace();
						}
					}
				}
			}

		}
}
