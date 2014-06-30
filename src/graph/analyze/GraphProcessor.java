package graph.analyze;

import edu.emory.mathcs.backport.java.util.Arrays;
import graph.common.CommonUtil;

import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.LineNumberReader;
import java.util.ArrayList;
import java.util.Calendar;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Queue;
import java.util.Vector;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.apache.xmlbeans.XmlException;
import org.apache.xmlbeans.XmlObject;
import org.dataandsearch.www.karma._2010._08.KarmaServiceStub;
import org.dataandsearch.www.karma.query._2010._10.DataProductIDListType;
import org.dataandsearch.www.karma.query._2010._10.GetDataProductDetailRequestDocument;
import org.dataandsearch.www.karma.query._2010._10.GetDataProductDetailRequestType;
import org.dataandsearch.www.karma.query._2010._10.GetDataProductDetailResponseDocument;
import org.dataandsearch.www.karma.query._2010._10.GetWorkflowGraphResponseDocument;
import org.openprovenance.model.v1_1_a.Agent;
import org.openprovenance.model.v1_1_a.Agents;
import org.openprovenance.model.v1_1_a.Artifact;
import org.openprovenance.model.v1_1_a.Artifacts;
import org.openprovenance.model.v1_1_a.CausalDependencies;
import org.openprovenance.model.v1_1_a.OPMGraph;
import org.openprovenance.model.v1_1_a.OTime;
import org.openprovenance.model.v1_1_a.Process;
import org.openprovenance.model.v1_1_a.Processes;
import org.openprovenance.model.v1_1_a.Property;
import org.openprovenance.model.v1_1_a.Used;
import org.openprovenance.model.v1_1_a.WasControlledBy;
import org.openprovenance.model.v1_1_a.WasDerivedFrom;
import org.openprovenance.model.v1_1_a.WasGeneratedBy;
import org.openprovenance.model.v1_1_a.WasTriggeredBy;

public class GraphProcessor {

	private HashMap<String, String[]> artifactsConfig;
	private HashMap<String, String[]> processesConfig;
	private HashMap<String, String[]> agentsConfig;
	private String[][] edgesConfig = null;
	private HashMap<String, String[]> terminatingConfig = null;
	private HashMap<String, String> processes = new HashMap<String, String>();
	private HashMap<String, String> artifacts = new HashMap<String, String>();
	private HashMap<String, String> agents = new HashMap<String, String>();
	private HashMap<String, String> visitedArtifacts = new HashMap<String, String>();
	private HashMap<String, String> visitedProcesses = new HashMap<String, String>();
	private HashMap<String, String> visitedAgents = new HashMap<String, String>();
	private HashMap<String, String> currentRunVisitedArtifacts = new HashMap<String, String>();
	private HashMap<String, String> currentRunVisitedProcesses = new HashMap<String, String>();
	private HashMap<String, String> currentRunVisitedAgents = new HashMap<String, String>();
	private HashMap<String, Integer> lookupAncestors = new HashMap<String, Integer>();

	private HashMap<String, String> agentsCertainty = new HashMap<String, String>();
	private HashMap<String, String> visitedVertices = new HashMap<String, String>();
	private HashMap<String, Double> nodeQScores = new HashMap<String, Double>();
	private HashMap<String, Double> edgeQScores = new HashMap<String, Double>();
	private HashMap<String, String> annotationsHash = new HashMap<String, String>();
	private Vector<Integer> globalEdgeCountPerGraph = new Vector<Integer>();
	private Vector<Integer> globalNodeCountPerGraph = new Vector<Integer>();

	private Queue<String> q;
	private Queue<String> q2;
	private Queue<String> q3;
	private Queue<String> firstPassInputVertices;
	private Queue<String> secondPassInputVertices;
	private boolean verbose = false;
	private int configSize = 2;
	private int nExpectedEdges = 0;
	private int nExpectedArtifacts = 0;
	private int nExpectedProcesses = 0;
	private int nExpectedAgents = 0;
	private static int counter = 1;
	private final String WF_URI_SUBS = "@wf#";

	private static final String ARTIFACT_WF_PREFIX = ":WorkFlowEmulator.Data.local:";
	private static final String WF_PREFIX = "http://bitternut.cs.indiana.edu:33000/";
	private static final String ARTIFACTS_CONFIG_FILE = "config/nam-wrf/artifacts-config.txt";
	private static final String PROCESSES_CONFIG_FILE = "config/nam-wrf/processes-config.txt";
	private static final String AGENTS_CONFIG_FILE = "config/nam-wrf/agents-config.txt";
	private static final String EDGES_CONFIG_FILE = "config/nam-wrf/edges-config.txt";
	private static final String TERMINATING_CONFIG_FILE = "config/nam-wrf/terminating-config.txt";
	private static final String ANNO_TYPES_OUTPUT_FILE = "config/output/annoTypesAnalyzer";
	private static final double EXP_CONST = 3;
	private static final double EXP_UPPER_BOUND = 1;

	public void printStructuralStats() {
		int edgeCountSize = globalEdgeCountPerGraph.size();
		Object[] edgesCount = globalEdgeCountPerGraph.toArray();
		edgeCountSize = edgesCount.length;
		Arrays.sort(edgesCount);

		// subtract one because we are index 0 based.
		double LQIndex = ((edgeCountSize + 1) / 4) - 1;
		double UQIndex = (3 * (edgeCountSize + 1) / 4) - 1;
		double medianIndex = ((edgeCountSize + 1) / 2) - 1;

		int Q1 = 0;
		int Q3 = 0;

		if (edgeCountSize >= 3) {
			if (Math.round(LQIndex) < LQIndex) {
				LQIndex = Math.round(LQIndex);
				Q1 = ((Integer) edgesCount[(int) LQIndex] + (Integer) edgesCount[(int) LQIndex + 1]) / 2;
			} else {
				System.out.println(LQIndex + " " + edgeCountSize);
				Q1 = (Integer) edgesCount[(int) LQIndex];
			}

			if (Math.round(UQIndex) > UQIndex) {
				UQIndex = Math.round(UQIndex);
				Q3 = ((Integer) edgesCount[(int) UQIndex] + (Integer) edgesCount[(int) UQIndex - 1]) / 2;
			} else {
				System.out.println(edgesCount[(int) UQIndex]);
				Q3 = (Integer) edgesCount[(int) UQIndex];
			}

			int IQR = Q3 - Q1;
			System.out.println("Q: " + Q3 + " " + Q1);
			double lowerFence = Q1 - (1.5 * IQR);
			double upperFence = Q3 + (1.5 * IQR);

			System.out.println("Fences: [" + lowerFence + "," + upperFence
					+ "]");

			// print outliers
			for (Object i : edgesCount) {
				int edgeCount = (Integer) i;

				if ((edgeCount < lowerFence) || (edgeCount > upperFence)) {
					System.out.println("Found outlier edgeCount" + edgeCount);
				}
			}

			int nodeCountSize = globalNodeCountPerGraph.size();
			Object[] nodesCount = globalNodeCountPerGraph.toArray();
			edgeCountSize = edgesCount.length;
			Arrays.sort(nodesCount);

			// subtract one because we are index 0 based.
			double nodeLQIndex = ((nodeCountSize + 1) / 4) - 1;
			double nodeUQIndex = (3 * (nodeCountSize + 1) / 4) - 1;
			double nodeMedianIndex = ((nodeCountSize + 1) / 2) - 1;

			int nodeQ1 = 0;
			int nodeQ3 = 0;
			if (Math.round(nodeLQIndex) < nodeLQIndex) {
				nodeLQIndex = Math.round(nodeLQIndex);
				nodeQ1 = ((Integer) nodesCount[(int) nodeLQIndex] + (Integer) nodesCount[(int) nodeLQIndex + 1]) / 2;
			} else {
				nodeQ1 = (Integer) nodesCount[(int) nodeLQIndex];
			}

			if (Math.round(nodeUQIndex) > nodeUQIndex) {
				nodeUQIndex = Math.round(nodeUQIndex);
				nodeQ3 = ((Integer) nodesCount[(int) nodeUQIndex] + (Integer) nodesCount[(int) nodeUQIndex - 1]) / 2;
			} else {
				System.out.println(nodesCount[(int) nodeUQIndex]);
				nodeQ3 = (Integer) nodesCount[(int) nodeUQIndex];
			}

			int nodeIQR = nodeQ3 - nodeQ1;
			System.out.println("Q: " + nodeQ3 + " " + nodeQ1);
			double nodeLowerFence = nodeQ1 - (1.5 * nodeIQR);
			double nodeUpperFence = nodeQ3 + (1.5 * nodeIQR);
			System.out.println(Arrays.toString(nodesCount));
			System.out.println("Fences: [" + nodeLowerFence + ","
					+ nodeUpperFence + "]");

			// print outliers
			for (Object i : nodesCount) {
				int nodeCount = (Integer) i;

				if ((nodeCount < nodeLowerFence)
						|| (nodeCount > nodeUpperFence)) {
					System.out.println("Found outlier nodeCount" + nodeCount);
				}
			}
		} else {
			System.err.println("Too little graphs to compare for outliers.");
		}
	}

	private void printOPMGraphStats(OPMGraph opmGraph, int nSubGraphs,
			boolean isFailedWorkflow) {
		CausalDependencies causalDependencies = opmGraph
				.getCausalDependencies();

		int sizeOfArtifactArray = opmGraph.getArtifacts().sizeOfArtifactArray();
		int sizeOfProcessArray = opmGraph.getProcesses().sizeOfProcessArray();
		int sizeOfAgentArray = opmGraph.getAgents().sizeOfAgentArray();
		int wasControlledByLength = causalDependencies
				.getWasControlledByArray().length;
		int wasDerivedFromLength = causalDependencies.getWasDerivedFromArray().length;
		int wasTriggeredByLength = causalDependencies.getWasTriggeredByArray().length;
		int wasGeneratedByLength = causalDependencies.getWasGeneratedByArray().length;
		int usedLength = causalDependencies.getUsedArray().length;
		int nVertices = sizeOfArtifactArray + sizeOfProcessArray;
		int nEdges = wasDerivedFromLength + wasTriggeredByLength
				+ wasGeneratedByLength + wasControlledByLength + usedLength;

		System.out.println("Number of artifacts: " + sizeOfArtifactArray + "/"
				+ nExpectedArtifacts);
		System.out.println("Number of processes: " + sizeOfProcessArray + "/"
				+ nExpectedProcesses);
		System.out.println("Number of agents: " + sizeOfAgentArray + "/"
				+ nExpectedAgents);
		System.out.println("WasDerivedFrom: " + wasDerivedFromLength);
		System.out.println("WasTriggeredBy: " + wasTriggeredByLength);
		System.out.println("WasControlledBy: " + wasControlledByLength);
		System.out.println("WasGeneratedBy: " + wasGeneratedByLength);
		System.out.println("Used: " + usedLength);
		System.out.println("Total number of vertices: " + nVertices + "/"
				+ (nExpectedArtifacts + nExpectedProcesses + nExpectedAgents));
		System.out.println("Total number of edges: " + nEdges + "/"
				+ nExpectedEdges);
		System.out.println("Number of subgraphs: " + nSubGraphs);
		System.out.println("Is failed workflow: " + isFailedWorkflow);
	}

	private Calendar[] findBestTimeRange(String cause, String effect,
			OPMGraph opmGraph) {

		Used[] usedArray = opmGraph.getCausalDependencies().getUsedArray();
		WasGeneratedBy[] wasGeneratedByArray = opmGraph.getCausalDependencies()
				.getWasGeneratedByArray();
		WasDerivedFrom[] wasDerivedFromArray = opmGraph.getCausalDependencies()
				.getWasDerivedFromArray();
		WasTriggeredBy[] wasTriggeredByArray = opmGraph.getCausalDependencies()
				.getWasTriggeredByArray();
		Calendar start = Calendar.getInstance();
		Calendar end = Calendar.getInstance();
		boolean isStartAdjusted = false;
		boolean isEndAdjusted = false;

		for (Used u : usedArray) {
			if (u.isSetTime()) {
				if (u.getEffect().getRef().equals(cause)) {
					if (u.getTime().isSetNoEarlierThan()) {
						Calendar noEarlierThan = u.getTime().getNoEarlierThan();
						if (!isStartAdjusted) {
							isStartAdjusted = true;
							start.setTimeInMillis(noEarlierThan
									.getTimeInMillis());
						} else if (start.after(noEarlierThan))
							start.setTimeInMillis(noEarlierThan
									.getTimeInMillis());
					}

					if (u.getTime().isSetExactlyAt()) {
						Calendar exactly = u.getTime().getExactlyAt();
						if (!isStartAdjusted) {
							isStartAdjusted = true;
							start.setTimeInMillis(exactly.getTimeInMillis());
						} else if (start.after(exactly))
							start.setTimeInMillis(exactly.getTimeInMillis());
					}

				}
				if (u.getCause().getRef().equals(effect)) {
					if (u.getTime().isSetNoLaterThan()) {
						Calendar noLaterThan = u.getTime().getNoLaterThan();
						if (!isEndAdjusted) {
							isEndAdjusted = true;
							end.setTimeInMillis(noLaterThan.getTimeInMillis());
						} else if (end.before(noLaterThan))
							end.setTimeInMillis(noLaterThan.getTimeInMillis());
					}

					if (u.getTime().isSetExactlyAt()) {
						Calendar exactly = u.getTime().getExactlyAt();
						if (!isEndAdjusted) {
							isEndAdjusted = true;
							end.setTimeInMillis(exactly.getTimeInMillis());
						} else if (end.before(exactly))
							end.setTimeInMillis(exactly.getTimeInMillis());
					}
				}
			}
		}

		for (WasTriggeredBy w : wasTriggeredByArray) {
			if (w.isSetTime()) {
				if (w.getEffect().getRef().equals(cause)) {
					if (w.getTime().isSetNoEarlierThan()) {
						Calendar noEarlierThan = w.getTime().getNoEarlierThan();
						if (!isStartAdjusted) {
							isStartAdjusted = true;
							start.setTimeInMillis(noEarlierThan
									.getTimeInMillis());
						} else if (start.after(noEarlierThan))
							start.setTimeInMillis(noEarlierThan
									.getTimeInMillis());
					}

					if (w.getTime().isSetExactlyAt()) {
						Calendar exactly = w.getTime().getExactlyAt();
						if (!isStartAdjusted) {
							isStartAdjusted = true;
							start.setTimeInMillis(exactly.getTimeInMillis());
						} else if (start.after(exactly))
							start.setTimeInMillis(exactly.getTimeInMillis());
					}

				}
				if (w.getCause().getRef().equals(effect)) {
					if (w.getTime().isSetNoLaterThan()) {
						Calendar noLaterThan = w.getTime().getNoLaterThan();
						if (!isEndAdjusted) {
							isEndAdjusted = true;
							end.setTimeInMillis(noLaterThan.getTimeInMillis());
						} else if (end.before(noLaterThan))
							end = noLaterThan;
					}

					if (w.getTime().isSetExactlyAt()) {
						Calendar exactly = w.getTime().getExactlyAt();
						if (!isEndAdjusted) {
							isEndAdjusted = true;
							end.setTimeInMillis(exactly.getTimeInMillis());
						} else if (end.before(exactly))
							end.setTimeInMillis(exactly.getTimeInMillis());
					}
				}
			}
		}

		for (WasGeneratedBy w : wasGeneratedByArray) {
			if (w.isSetTime()) {
				if (w.getEffect().getRef().equals(cause)) {
					if (w.getTime().isSetNoEarlierThan()) {
						Calendar noEarlierThan = w.getTime().getNoEarlierThan();
						if (!isStartAdjusted) {
							isStartAdjusted = true;
							start.setTimeInMillis(noEarlierThan
									.getTimeInMillis());
						} else if (start.after(noEarlierThan))
							start.setTimeInMillis(noEarlierThan
									.getTimeInMillis());
					}

					if (w.getTime().isSetExactlyAt()) {
						Calendar exactly = w.getTime().getExactlyAt();
						if (!isStartAdjusted) {
							isStartAdjusted = true;
							start.setTimeInMillis(exactly.getTimeInMillis());
						} else if (start.after(exactly))
							start.setTimeInMillis(exactly.getTimeInMillis());
					}

				}
				if (w.getCause().getRef().equals(effect)) {
					if (w.getTime().isSetNoLaterThan()) {
						Calendar noLaterThan = w.getTime().getNoLaterThan();
						if (!isEndAdjusted) {
							isEndAdjusted = true;
							end.setTimeInMillis(noLaterThan.getTimeInMillis());
						} else if (end.before(noLaterThan))
							end = noLaterThan;
					}

					if (w.getTime().isSetExactlyAt()) {
						Calendar exactly = w.getTime().getExactlyAt();
						if (!isEndAdjusted) {
							isEndAdjusted = true;
							end.setTimeInMillis(exactly.getTimeInMillis());
						} else if (end.before(exactly))
							end.setTimeInMillis(exactly.getTimeInMillis());
					}
				}
			}
		}

		for (WasDerivedFrom w : wasDerivedFromArray) {
			if (w.isSetTime()) {
				if (w.getEffect().getRef().equals(cause)) {
					if (w.getTime().isSetNoEarlierThan()) {
						Calendar noEarlierThan = w.getTime().getNoEarlierThan();
						if (!isStartAdjusted) {
							isStartAdjusted = true;
							start.setTimeInMillis(noEarlierThan
									.getTimeInMillis());
						} else if (start.after(noEarlierThan))
							start.setTimeInMillis(noEarlierThan
									.getTimeInMillis());
					}

					if (w.getTime().isSetExactlyAt()) {
						Calendar exactly = w.getTime().getExactlyAt();
						if (!isStartAdjusted) {
							isStartAdjusted = true;
							start.setTimeInMillis(exactly.getTimeInMillis());
						} else if (start.after(exactly))
							start.setTimeInMillis(exactly.getTimeInMillis());
					}

				}
				if (w.getCause().getRef().equals(effect)) {
					if (w.getTime().isSetNoLaterThan()) {
						Calendar noLaterThan = w.getTime().getNoLaterThan();
						if (!isEndAdjusted) {
							isEndAdjusted = true;
							end.setTimeInMillis(noLaterThan.getTimeInMillis());
						} else if (end.before(noLaterThan))
							end = noLaterThan;
					}

					if (w.getTime().isSetExactlyAt()) {
						Calendar exactly = w.getTime().getExactlyAt();
						if (!isEndAdjusted) {
							isEndAdjusted = true;
							end.setTimeInMillis(exactly.getTimeInMillis());
						} else if (end.before(exactly))
							end.setTimeInMillis(exactly.getTimeInMillis());
					}
				}
			}
		}

		System.out.println("Time: " + start.getTime() + " " + end.getTime());

		Calendar[] range = new Calendar[2];
		if (isStartAdjusted)
			range[0] = start;

		if (isEndAdjusted)
			range[1] = end;

		return range;
	}

	private void readConfigFile(String fileName,
			HashMap<String, String[]> configHash, String contextWfURI) {
		FileReader fileRead;
		LineNumberReader lineReader;
		String nextLine = null;
		try {
			fileRead = new FileReader(fileName);

			lineReader = new LineNumberReader(fileRead);
			nextLine = null;

			while ((nextLine = lineReader.readLine()) != null) {

				String[] split = nextLine.split(" ");
				String[] config = new String[configSize];
				for (int i = 0; i < configSize; i++) {
					config[i] = split[i + 1];
				}

				if (split[0].contains(WF_URI_SUBS))
					split[0] = split[0]
							.replace(WF_URI_SUBS, contextWfURI + "_");

				configHash.put(split[0], config);
			}

			lineReader.close();
			fileRead.close();
		} catch (FileNotFoundException e) {
			System.err.println("Error: Missing configuration file.");
		} catch (IOException e) {
			System.err.println("Error: IO Exception.");
		}
	}

	private int calcDamLevDistance(String s1, String s2) {
		int[][] d = new int[s1.length() + 1][s2.length() + 1];
		int cost = 0;

		for (int i = 0; i <= s1.length(); i++)
			d[i][0] = i;

		for (int j = 1; j <= s2.length(); j++)
			d[0][j] = j;

		for (int i = 1; i <= s1.length(); i++) {
			for (int j = 1; j <= s2.length(); j++) {
				if (s1.charAt(i - 1) == s2.charAt(j - 1))
					cost = 0;
				else
					cost = 1;
				d[i][j] = Math.min(Math.min(d[i - 1][j] + 1, d[i][j - 1] + 1),
						d[i - 1][j - 1] + cost);

				if (i > 1 && j > 1 && s1.charAt(i - 1) == s2.charAt(j - 2)
						&& s1.charAt(i - 2) == s2.charAt(j - 1)) {
					d[i][j] = Math.min(d[i][j], d[i - 2][j - 2] + cost);
				}
			}
		}

		return d[s1.length()][s2.length()];
	}

	int partition(int arr[], String ids[], int left, int right) {
		int i = left, j = right;
		int tmp;
		String tmpStr;
		int pivot = arr[(left + right) / 2];

		while (i <= j) {
			while (arr[i] < pivot)
				i++;
			while (arr[j] > pivot)
				j--;
			if (i <= j) {
				tmp = arr[i];
				arr[i] = arr[j];
				arr[j] = tmp;
				tmpStr = ids[i];
				ids[i] = ids[j];
				ids[j] = tmpStr;

				i++;
				j--;
			}
		}

		return i;
	}

	private void quickSortQueue(int arr[], String ids[], int left, int right) {
		int index = partition(arr, ids, left, right);
		if (left < index - 1)
			quickSortQueue(arr, ids, left, index - 1);
		if (index < right)
			quickSortQueue(arr, ids, index, right);
	}

	private int firstQueueProcessor(Queue<String> q, OPMGraph opmGraph,
			String contextWfURI) {
		boolean isLinked = false;
		int nSubGraphs = 0;

		while (!q.isEmpty()) {

			if (q.peek() != null) {

				if (q.peek().contains("Process")) {

					if (processTraversal(q.poll(), opmGraph, contextWfURI))
						isLinked = true;

				} else {

					if (artifactTraversal(q.poll(), opmGraph, contextWfURI))
						isLinked = true;
				}
			}
		}

		if (!isLinked) {
			nSubGraphs++;
		}

		// copy all current run artifacts and processes to global
		visitedArtifacts.putAll(currentRunVisitedArtifacts);
		visitedProcesses.putAll(currentRunVisitedProcesses);
		visitedAgents.putAll(currentRunVisitedAgents);

		for (Object a : currentRunVisitedArtifacts.keySet().toArray()) {
			currentRunVisitedArtifacts.remove(a);
		}
		for (Object p : currentRunVisitedProcesses.keySet().toArray()) {
			currentRunVisitedProcesses.remove(p);
		}

		return nSubGraphs;

	}

	private int secondQueueProcessor(Queue<String> q, OPMGraph opmGraph,
			boolean useFix, String contextWfURI) {
		int nErrors = 0;
		while (!q2.isEmpty()) {

			if (q2.peek() != null) {

				if (q2.peek().contains("Process")) {

					nErrors += processVisitor(q.poll(), opmGraph, useFix,
							contextWfURI);

				} else {

					nErrors += artifactVisitor(q.poll(), opmGraph, useFix,
							contextWfURI);
				}
			}

			Object[] array = q2.toArray();
			int[] nAncestors = new int[array.length];
			String[] ids = new String[array.length];

			for (int i = 0; i < array.length; i++) {
				if (lookupAncestors.get(array[i]) != null) {
					nAncestors[i] = lookupAncestors.get(array[i]);
					ids[i] = (String) array[i];
				}

			}
		}

		return nErrors;

	}

	public Object[] graphProcesor(KarmaServiceStub stub, String contextWfURI,
			OPMGraph opmGraph) throws XmlException, FileNotFoundException,
			IOException {

		artifactsConfig = new HashMap<String, String[]>();
		processesConfig = new HashMap<String, String[]>();
		terminatingConfig = new HashMap<String, String[]>();

		q = new LinkedList<String>();
		q2 = new LinkedList<String>();
		q3 = new LinkedList<String>();
		firstPassInputVertices = new LinkedList<String>();
		secondPassInputVertices = new LinkedList<String>();

		boolean isFailedWorkflow = true;
		int nArtifacts = 0;
		int nProcesses = 0;
		int nVertices = 0;
		int nEdges = 0;
		int nSubGraphs = 0;
		int nErrors = 0;

		CausalDependencies causalDependencies = opmGraph
				.getCausalDependencies();
		Used[] usedArray = causalDependencies.getUsedArray();
		WasDerivedFrom[] wasDerivedFromArray = causalDependencies
				.getWasDerivedFromArray();
		WasGeneratedBy[] wasGeneratedByArray = causalDependencies
				.getWasGeneratedByArray();
		WasTriggeredBy[] wasTriggeredByArray = causalDependencies
				.getWasTriggeredByArray();
		WasControlledBy[] wasControlledByArray = causalDependencies
				.getWasControlledByArray();

		readConfigFile(ARTIFACTS_CONFIG_FILE, artifactsConfig, contextWfURI);
		readConfigFile(PROCESSES_CONFIG_FILE, processesConfig, contextWfURI);
		readConfigFile(TERMINATING_CONFIG_FILE, terminatingConfig, contextWfURI);

		try {

			FileReader fileRead;
			LineNumberReader lineReader;
			String nextLine = null;

			fileRead = new FileReader(EDGES_CONFIG_FILE);
			lineReader = new LineNumberReader(fileRead);
			nextLine = null;
			nExpectedEdges = 0;
			while ((nextLine = lineReader.readLine()) != null)
				nExpectedEdges++;

			edgesConfig = new String[nExpectedEdges][configSize];

			int i = 0;
			lineReader.close();
			fileRead.close();
			fileRead = new FileReader(EDGES_CONFIG_FILE);
			lineReader = new LineNumberReader(fileRead);

			while ((nextLine = lineReader.readLine()) != null) {

				String[] split = nextLine.split(" ");
				if (split[0].contains("@wf")) {
					edgesConfig[i][0] = split[0].replace(WF_URI_SUBS,
							contextWfURI + "_");
				} else {
					edgesConfig[i][0] = split[0];
				}

				if (split[1].equals("@wf")) {
					edgesConfig[i++][1] = split[1].replace(WF_URI_SUBS,
							contextWfURI + "_");
				} else {
					edgesConfig[i++][1] = split[1];
				}
			}

			lineReader.close();
			fileRead.close();

		} catch (FileNotFoundException e) {
			System.err.println("Error: Missing configuration file.");
		} catch (IOException e) {
			System.err.println("Error: IO Exception.");
		}

		// Check number of processes. If process is an input process, put in
		// queue of input vertices.
		for (Process process : opmGraph.getProcesses().getProcessArray()) {
			String processID = process.getId();

			if (processes.get(processID) == null) {
				if (process.getAnnotationArray().length == 0) {

				} else {
					Property[] propertyArray = process.getAnnotationArray()[0]
							.getPropertyArray();

					for (Property p : propertyArray) {
						String value = p.getValue().toString();

						if (value.contains("workflowNodeID")) {
							Pattern pattern = Pattern.compile(">.*<");
							Matcher m = pattern.matcher(value);

							String wfNodeID = null;
							String serviceID = null;
							if (m.find()) {
								wfNodeID = m.group().replace(">", "")
										.replace("<", "");
							}

							for (Property p1 : propertyArray) {
								String value1 = p1.getValue().toString();
								if (value1.contains("serviceID")) {

									m = pattern.matcher(value1);
									if (m.find()) {
										serviceID = m.group().replace(">", "")
												.replace("<", "");
										System.err.println(serviceID
												+ " "
												+ calcDamLevDistance(serviceID,
														WF_PREFIX));
									}
								}
							}

							if (serviceID.equals(contextWfURI)) {
								processes.put(processID, contextWfURI + "_"
										+ wfNodeID);
							} else {
								processes.put(processID, wfNodeID);
							}

							if (terminatingConfig.containsKey(serviceID)) {
								isFailedWorkflow = false;
							}

							boolean isWasTriggeredBy = false;
							boolean isUsed = false;

							for (WasTriggeredBy w : wasTriggeredByArray) {
								if (w.getEffect().getRef().equals(processID)) {
									isWasTriggeredBy = true;
									break;
								}
							}

							for (Used u : usedArray) {
								if (u.getEffect().getRef().equals(processID)) {
									isUsed = true;
									break;
								}
							}

							if (!isWasTriggeredBy && !isUsed) {
								if (verbose)
									System.out.println("Input process: "
											+ processID + " " + serviceID + " "
											+ wfNodeID);
								firstPassInputVertices.add(processID);
								lookupAncestors.put(processID, 0);
							}

							nProcesses++;
						}
					}
				}
			}
		}

		nExpectedArtifacts = artifactsConfig.size();
		nExpectedProcesses = processesConfig.size();

		// Check number of artifacts. If artifact is an input artifact, put in
		// queue of input vertices.
		for (Artifact artifact : opmGraph.getArtifacts().getArtifactArray()) {
			GetDataProductDetailRequestDocument getDataProductDetail = GetDataProductDetailRequestDocument.Factory
					.newInstance();
			GetDataProductDetailRequestType dataProductDetailRequest = getDataProductDetail
					.addNewGetDataProductDetailRequest();
			DataProductIDListType dataProductIDList = dataProductDetailRequest
					.addNewDataProductIDList();
			dataProductIDList.addDataProductID(artifact.getId());
			GetDataProductDetailResponseDocument getDataProductDetailResponseDocument = null;
			if (stub != null) {
				getDataProductDetailResponseDocument = stub
						.getDataProductDetail(getDataProductDetail);
			}
			String id = artifact.getId();

			if (artifacts.get(id) == null) {
				if (getDataProductDetailResponseDocument != null) {
					artifacts.put(
							id,
							getDataProductDetailResponseDocument
									.getGetDataProductDetailResponse()
									.getDataProductDetailList()
									.getDataProductDetailArray(0).getFileURI()
									.replace(contextWfURI, "")
									.replace(ARTIFACT_WF_PREFIX, ""));
				} else {
					// input artifact?
					artifacts.put(id, id);
				}
				if (terminatingConfig.containsKey(artifacts.get(id))) {
					isFailedWorkflow = false;
				}

				boolean isWasDerivedFrom = false;
				boolean isWasGeneratedBy = false;

				for (WasDerivedFrom w : wasDerivedFromArray) {
					if (w.getEffect().getRef().equals(id)) {
						isWasDerivedFrom = true;
						break;
					}
				}

				for (WasGeneratedBy w : wasGeneratedByArray) {
					if (w.getEffect().getRef().equals(id)) {
						isWasGeneratedBy = true;
						break;
					}
				}

				if (!isWasDerivedFrom && !isWasGeneratedBy) {
					if (verbose)
						System.out.println("Input artifact: " + id);

					firstPassInputVertices.add(id);
					lookupAncestors.put(id, 0);
				}

				nArtifacts++;
			}
		}

		for (int i = 0; i < wasTriggeredByArray.length; i++) {

		}

		nVertices = (nArtifacts + nProcesses);
		nEdges = (wasDerivedFromArray.length + wasTriggeredByArray.length
				+ usedArray.length + wasControlledByArray.length + wasGeneratedByArray.length);

		/* TODO: Use Topological sorting to check for cycles */
		// List<String> list = new ArrayList<String>();
		// List<String> inputVertices = new ArrayList<String>();
		// Vector<String> edges = new Vector<String>();
		//
		// for (int i = 0; i < wasTriggeredByArray.length; i++) {
		// String edgeName = wasTriggeredByArray[i].getCause().getRef() + "<-"
		// + wasTriggeredByArray[i].getEffect().getRef();
		// edges.add(edgeName);
		// }
		// for (int i = 0; i < wasDerivedFromArray.length; i++) {
		// String edgeName = wasDerivedFromArray[i].getCause().getRef() + "<-"
		// + wasDerivedFromArray[i].getEffect().getRef();
		// edges.add(edgeName);
		// }
		// for (int i = 0; i < wasControlledByArray.length; i++) {
		// String edgeName = wasControlledByArray[i].getCause().getRef() + "<-"
		// + wasControlledByArray[i].getEffect().getRef();
		// edges.add(edgeName);
		// }
		// for (int i = 0; i < usedArray.length; i++) {
		// String edgeName = usedArray[i].getCause().getRef() + "<-"
		// + usedArray[i].getEffect().getRef();
		// edges.add(edgeName);
		// }
		// for (int i = 0; i < wasGeneratedByArray.length; i++) {
		// String edgeName = wasGeneratedByArray[i].getCause().getRef() + "<-"
		// + wasGeneratedByArray[i].getEffect().getRef();
		// edges.add(edgeName);
		// }
		//
		// inputVertices.addAll(firstPassInputVertices);
		// while (!inputVertices.isEmpty()) {
		// String node = inputVertices.remove(0);
		// list.add(node);
		//
		// for (int i = 0; i < edges.toArray().length; i++) {
		//
		// if (((String) edges.toArray()[i]).startsWith(node)) {
		// String edge = edges.remove(i);
		// String effectNode = edge.replace("<-", "")
		// .replace(node, "");
		//
		// boolean hasIncomingEdge = false;
		// System.out.println(edges.size());
		// for (int j = 0; j < edges.toArray().length; j++) {
		// if (((String) edges.toArray()[j]).endsWith(effectNode)) {
		// hasIncomingEdge = true;
		// }
		// }
		//
		// if (!hasIncomingEdge) {
		// inputVertices.add(effectNode);
		// }
		//
		// }
		// }
		// }
		//
		// if (edges.isEmpty()) {
		// System.out.println("No cycles!!");
		// } else {
		// System.out.println("Has cycles!!");
		// for (int i = 0; i < list.size(); i++) {
		// System.out.println(list.toArray()[i]);
		// }
		// }

		/* 1st pass: Identifies number of subgraphs */
		secondPassInputVertices.addAll(firstPassInputVertices);

		while (!firstPassInputVertices.isEmpty()) {
			// Put input vertices into processing queue.
			if (verbose)
				System.out.println("@Adding input vertex: "
						+ firstPassInputVertices.peek());
			q.add(firstPassInputVertices.poll());
			nSubGraphs += firstQueueProcessor(q, opmGraph, contextWfURI);

		}

		for (Object a : artifacts.keySet().toArray()) {
			if (!visitedArtifacts.containsKey(a)) {
				q.add(a.toString());
				int pr = firstQueueProcessor(q, opmGraph, contextWfURI);
				nSubGraphs += pr;
			}
		}

		for (Object p : processes.keySet().toArray()) {
			if (!visitedProcesses.containsKey(p)) {
				q.add(p.toString());
				int pr = firstQueueProcessor(q, opmGraph, contextWfURI);
				nSubGraphs += pr;
				System.out.println("#" + nSubGraphs);
			}
		}

		firstPassInputVertices.addAll(secondPassInputVertices);
		while (!secondPassInputVertices.isEmpty()) {
			// Put input vertices into processing queue.
			if (verbose)
				System.out.println("@Adding input vertex: "
						+ secondPassInputVertices.peek());
			q2.add(secondPassInputVertices.poll());

		}

		/* 2nd pass: Identifies order of nodes in graph */

		nErrors = secondQueueProcessor(q2, opmGraph, false, contextWfURI);

		int values[] = new int[lookupAncestors.keySet().size()];
		String keys[] = new String[lookupAncestors.keySet().size()];
		for (int i = 0; i < lookupAncestors.keySet().size(); i++) {
			values[i] = (Integer) lookupAncestors.values().toArray()[i];
			keys[i] = (String) lookupAncestors.keySet().toArray()[i];
		}
		quickSortQueue(values, keys, 0, values.length - 1);

		for (int i = 0; i < lookupAncestors.keySet().size(); i++) {
//			System.out.println(": " + keys[i] + " : " + values[i]);
			q3.add(keys[i]);
		}

		double totalNodeQScores = 0;
		double totalEdgeQScores = 0;
		for (int i = 0; i < nodeQScores.keySet().size(); i++) {
//			System.out.println(": " + nodeQScores.keySet().toArray()[i] + " : "
//					+ nodeQScores.values().toArray()[i]);
			totalNodeQScores += nodeQScores
					.get(nodeQScores.keySet().toArray()[i]);
		}

		for (int i = 0; i < edgeQScores.keySet().size(); i++) {
//			System.out.println(": " + edgeQScores.keySet().toArray()[i] + " : "
//					+ edgeQScores.values().toArray()[i]);
			totalEdgeQScores += edgeQScores
					.get(edgeQScores.keySet().toArray()[i]);
		}

		if (verbose) {
			printOPMGraphStats(opmGraph, nSubGraphs, isFailedWorkflow);
		}

		double scoreBefore = (totalNodeQScores + totalEdgeQScores)
				/ (nExpectedEdges + nExpectedArtifacts + nExpectedProcesses);
		System.err.println(totalNodeQScores + " " + totalEdgeQScores);
		Object[] graphAttributes = new Object[11];
		graphAttributes[0] = nVertices;
		graphAttributes[1] = nEdges;
		graphAttributes[2] = nSubGraphs;
		graphAttributes[3] = isFailedWorkflow;
		graphAttributes[4] = scoreBefore;

		/* 3rd pass: Actual evaluation */
		System.out.println("------------------------");
		nodeQScores.keySet().clear();
		nodeQScores.values().clear();
		edgeQScores.keySet().clear();
		edgeQScores.values().clear();
		// nodeQScores = new HashMap<String, Double>();

		secondPassInputVertices.addAll(firstPassInputVertices);
		while (!secondPassInputVertices.isEmpty()) {
			// Put input vertices into processing queue.
			q2.add(secondPassInputVertices.poll());

		}

		nErrors = secondQueueProcessor(q2, opmGraph, true, contextWfURI);

		// Reset stuff
		totalNodeQScores = 0;
		totalEdgeQScores = 0;
		nEdges = 0;
		nVertices = 0;
		nSubGraphs = 0;
		visitedArtifacts.clear();
		visitedProcesses.clear();
		currentRunVisitedArtifacts.clear();
		currentRunVisitedProcesses.clear();
		while (!firstPassInputVertices.isEmpty()) {
			// Put input vertices into processing queue.
			q.add(firstPassInputVertices.poll());
			nSubGraphs += firstQueueProcessor(q, opmGraph, contextWfURI);

		}

		for (Object a : artifacts.keySet().toArray()) {
			if (!visitedArtifacts.containsKey(a)) {
				q.add(a.toString());
				int pr = firstQueueProcessor(q, opmGraph, contextWfURI);
				nSubGraphs += pr;
			}
		}

		for (Object p : processes.keySet().toArray()) {
			if (!visitedProcesses.containsKey(p)) {
				q.add(p.toString());
				int pr = firstQueueProcessor(q, opmGraph, contextWfURI);
				nSubGraphs += pr;
				System.out.println("#" + nSubGraphs);
			}
		}

		// for (int i = 0; i < lookupAncestors.keySet().size(); i++) {
		//
		// System.out.println(lookupAncestors.keySet().toArray()[i] + " " + i +
		// " " + lookupAncestors.values().toArray().length);
		// System.out.println(lookupAncestors.values().toArray()[i] + " " +
		// lookupAncestors.keySet().toArray().length);
		// System.out.println(values.length + " " + keys.length);
		// values[i] = (Integer) lookupAncestors.values().toArray()[i];
		// keys[i] = (String) lookupAncestors.keySet().toArray()[i];
		// }
		// quickSortQueue(values, keys, 0, values.length - 1);
		//
		// for (int i = 0; i < lookupAncestors.keySet().size(); i++) {
		// System.out.println(": " + keys[i] + " : " + values[i]);
		// q3.add(keys[i]);
		// }

		for (int i = 0; i < nodeQScores.keySet().size(); i++) {
			System.out.println(": " + nodeQScores.keySet().toArray()[i] + " : "
					+ nodeQScores.values().toArray()[i]);
			totalNodeQScores += nodeQScores
					.get(nodeQScores.keySet().toArray()[i]);

		}

		for (int i = 0; i < edgeQScores.keySet().size(); i++) {
			totalEdgeQScores += edgeQScores
					.get(edgeQScores.keySet().toArray()[i]);

		}
		ErrorDetector errorDetector = new ErrorDetector();
		errorDetector.getAnnoAnalysis();
		double graphNodeQScore = 1.0;
		double nGraphNodeErrors = 0;
		nGraphNodeErrors = errorDetector.getTemporalAnalysis(contextWfURI);
		// thirdQueueProcessor(q3, wasGeneratedByArray, wasTriggeredByArray,
		// wasDerivedFromArray, usedArray, opmGraph);
		nVertices = (opmGraph.getArtifacts().sizeOfArtifactArray() + opmGraph
				.getProcesses().sizeOfProcessArray());
		nEdges = opmGraph.getCausalDependencies().getWasDerivedFromArray().length
				+ opmGraph.getCausalDependencies().getWasTriggeredByArray().length
				+ opmGraph.getCausalDependencies().getUsedArray().length
				+ opmGraph.getCausalDependencies().getWasControlledByArray().length
				+ opmGraph.getCausalDependencies().getWasGeneratedByArray().length;
		if (true) {
			printOPMGraphStats(opmGraph, nSubGraphs, isFailedWorkflow);
		}
		// System.err.println(opmGraph);
		double scoreAfter = ((totalNodeQScores + totalEdgeQScores + graphNodeQScore) / (nExpectedEdges
				+ nExpectedArtifacts + nExpectedProcesses + 1));

		graphAttributes[5] = nVertices;
		graphAttributes[6] = nEdges;
		graphAttributes[7] = nSubGraphs;
		graphAttributes[8] = nErrors;
		graphAttributes[9] = scoreAfter;
		graphAttributes[10] = opmGraph;

		globalEdgeCountPerGraph.add(nEdges);
		globalNodeCountPerGraph.add(nVertices);

		try {
			FileWriter annoTypesOutput = new FileWriter(ANNO_TYPES_OUTPUT_FILE
					+ contextWfURI.replace(":", "+").replace("/", "_") + ".txt");
			for (Object a : annotationsHash.keySet().toArray()) {
				annoTypesOutput.append(a.toString() + "\n");
			}

			annoTypesOutput.flush();
			annoTypesOutput.close();
		} catch (Exception e) {
			e.printStackTrace();
			System.err
					.println("Error in writing annotation types to output file.");
		}

		return graphAttributes;
	}

	private boolean processTraversal(String processID, OPMGraph opmGraph,
			String contextWfURI) {

		int nOutEdges = 0;
		int nInEdges = 0;
		int nErrors = 0;
		boolean isLinked = false;

		CommonUtil util = new CommonUtil();
		Vector<String> linkedEdges = new Vector<String>();
		ErrorDetector errorDetector = new ErrorDetector();
		String[] pConfig = processesConfig.get(processes.get(processID));
		Processes opmProcesses = opmGraph.getProcesses();
		WasGeneratedBy[] wasGeneratedBy = opmGraph.getCausalDependencies()
				.getWasGeneratedByArray();
		WasTriggeredBy[] wasTriggeredBy = opmGraph.getCausalDependencies()
				.getWasTriggeredByArray();
		Used[] used = opmGraph.getCausalDependencies().getUsedArray();

		if (currentRunVisitedProcesses.get(processID) == null) {
			currentRunVisitedProcesses.put(processID, processID);
			System.out.println("Visited process: " + processID);

			Process[] processArray = opmProcesses.getProcessArray();
			for (Process p : processArray) {
				if (p.getId().equals(processID)) {
					nErrors += errorDetector.annotationAnalyzer(contextWfURI,
							processID, Process.class.getSimpleName(),
							p.getAnnotationArray(), annotationsHash);
				}
			}

			for (WasGeneratedBy w : wasGeneratedBy) {
				if (w.getCause().getRef().equals(processID)) {
					String effect = w.getEffect().getRef();
					if (visitedArtifacts.get(effect) == null) {
						if (!q.contains(effect))
							q.add(effect);

					} else {
						System.out.println("\tVisited artifacts? "
								+ w.getEffect().getRef());
						isLinked = true;
					}
					linkedEdges.add(w.getEffect().getRef());

					// Measure edge quality here

					double nEdgeErrors = 0;
					int nEdgeTimestampErrors = errorDetector
							.edgeTimestampErrorDetector(contextWfURI, w);
					nEdgeErrors += nEdgeTimestampErrors;
					edgeQScores.put(util.createCausalRelationshipIDs(w
							.getCause().getRef(), w.getEffect().getRef()),
							((nEdgeErrors / -EXP_CONST) + EXP_UPPER_BOUND));
					nOutEdges++;
				}

				if (w.getEffect().getRef().equals(processID)) {
					// Measure edge quality here

					double nEdgeErrors = 0;
					int nEdgeTimestampErrors = errorDetector
							.edgeTimestampErrorDetector(contextWfURI, w);
					nEdgeErrors += nEdgeTimestampErrors;
					edgeQScores.put(util.createCausalRelationshipIDs(w
							.getCause().getRef(), w.getEffect().getRef()),
							((nEdgeErrors / -EXP_CONST) + EXP_UPPER_BOUND));
					nInEdges++;
				}
			}

			for (Used u : used) {
				if (u.getEffect().getRef().equals(processID)) {

					// Measure edge quality here

					double nEdgeErrors = 0;
					int nEdgeTimestampErrors = errorDetector
							.edgeTimestampErrorDetector(contextWfURI, u);
					nEdgeErrors += nEdgeTimestampErrors;
					edgeQScores.put(util.createCausalRelationshipIDs(u
							.getCause().getRef(), u.getEffect().getRef()),
							((nEdgeErrors / -EXP_CONST) + EXP_UPPER_BOUND));
					nInEdges++;
				}
			}

			for (WasTriggeredBy w : wasTriggeredBy) {
				if (w.getCause().getRef().equals(processID)) {
					String effect = w.getEffect().getRef();
					if (visitedProcesses.get(effect) == null) {
						if (!q.contains(effect))
							q.add(effect);

					} else {
						// System.out.println("\tVisited process? "
						// + w.getEffect().getRef());
						isLinked = true;
					}
					linkedEdges.add(w.getEffect().getRef());

					// Measure edge quality here

					double nEdgeErrors = 0;
					int nEdgeTimestampErrors = errorDetector
							.edgeTimestampErrorDetector(contextWfURI, w);
					nEdgeErrors += nEdgeTimestampErrors;
					edgeQScores.put(util.createCausalRelationshipIDs(w
							.getCause().getRef(), w.getEffect().getRef()),
							((nEdgeErrors / -EXP_CONST) + EXP_UPPER_BOUND));
					nOutEdges++;

				}

				if (w.getEffect().getRef().equals(processID)) {
					// Measure edge quality here

					double nEdgeErrors = 0;
					int nEdgeTimestampErrors = errorDetector
							.edgeTimestampErrorDetector(contextWfURI, w);
					nEdgeErrors += nEdgeTimestampErrors;
					edgeQScores.put(util.createCausalRelationshipIDs(w
							.getCause().getRef(), w.getEffect().getRef()),
							((nEdgeErrors / -EXP_CONST) + EXP_UPPER_BOUND));
					nInEdges++;
				}
			}
			System.out.println("##: " + processID + " " + " " + nInEdges);
			if (pConfig != null) {
				int expectedOutEdges = Integer.parseInt(pConfig[1]);
				int expectedInEdges = Integer.parseInt(pConfig[0]);
				Vector<String> outCandidates = new Vector<String>();
				if (expectedInEdges != nInEdges) {
					//
					// System.out.println("\tMissing in-edge(s) for process: "
					// + processID + ". Expected number of in-edge(s): "
					// + expectedInEdges + ". Actual: " + nInEdges);

				}

				if (expectedOutEdges != nOutEdges) {

					// System.out.println("\tMissing out-edge(s) for process: "
					// + processID + ". Expected number of out-edge(s): "
					// + expectedOutEdges + ". Actual: " + nOutEdges);
					//
					// Object[] pKeys = processes.keySet().toArray();
					// Object[] pValues = processes.values().toArray();
					// Object[] aKeys = artifacts.keySet().toArray();
					// Object[] aValues = artifacts.values().toArray();
					// for (int i = 0; i < nExpectedEdges; i++) {
					//
					// if ((processes.get(processID))
					// .equals(edgesConfig[i][0])) {
					//
					// for (int j = 0; j < pKeys.length; j++) {
					//
					// if (pValues[j].equals(edgesConfig[i][1])
					// && !linkedEdges.contains(pKeys[j])) {
					// outCandidates.add(pKeys[j].toString());
					// // System.out.println("##" + pKeys[j]);
					// }
					// }
					//
					// for (int j = 0; j < aKeys.length; j++) {
					// // System.out
					// // .println("::" + aKeys[j] + aValues[j]);
					// if (aValues[j].equals(edgesConfig[i][1])
					// && !linkedEdges.contains(aKeys[j])) {
					// outCandidates.add(aKeys[j].toString());
					// // System.out.println("##" + aKeys[j]);
					//
					// }
					// }
					// }
					// }

					// GraphAnnotator ga = new GraphAnnotator();
					// ga.processAnnotator(processID,
					// (expectedOutEdges - nOutEdges), outCandidates,
					// opmGraph, true);

				} else {

					System.out.println("\tExpected number of out-edge(s) for "
							+ processID + " detected: " + nOutEdges);
				}

				nErrors = (expectedInEdges - nInEdges)
						+ (expectedOutEdges - nOutEdges);
				nodeQScores.put(processID,
						((nErrors / -EXP_CONST) + EXP_UPPER_BOUND));
			}
		}

		return isLinked;
	}

	private boolean artifactTraversal(String artifactID, OPMGraph opmGraph,
			String contextWfURI) {

		int nOutEdges = 0;
		int nInEdges = 0;
		int nErrors = 0;
		boolean isLinked = false;

		CommonUtil util = new CommonUtil();
		Vector<String> linkedEdges = new Vector<String>();
		Vector<String> childProcesses = new Vector<String>();
		String[] aConfig = artifactsConfig.get(artifacts.get(artifactID));
		ErrorDetector errorDetector = new ErrorDetector();
		Artifacts opmArtifacts = opmGraph.getArtifacts();
		WasGeneratedBy[] wasGeneratedBy = opmGraph.getCausalDependencies()
				.getWasGeneratedByArray();
		WasDerivedFrom[] wasDerivedFrom = opmGraph.getCausalDependencies()
				.getWasDerivedFromArray();
		Used[] used = opmGraph.getCausalDependencies().getUsedArray();

		if (currentRunVisitedArtifacts.get(artifactID) == null) {

			currentRunVisitedArtifacts.put(artifactID, artifactID);

			Artifact[] artifactArray = opmArtifacts.getArtifactArray();
			for (Artifact a : artifactArray) {
				if (a.getId().equals(artifactID)) {
					nErrors += errorDetector.annotationAnalyzer(contextWfURI,
							artifactID, Artifact.class.getSimpleName(),
							a.getAnnotationArray(), annotationsHash);
				}
			}

			for (Used w : used) {
				if (w.getCause().getRef().equals(artifactID)) {
					String effect = w.getEffect().getRef();
					if (visitedProcesses.get(effect) == null) {
						if (!q.contains(effect)) {
							q.add(effect);
						}

						childProcesses.add(effect);

					} else {
						// System.out.println("\tVisited process? "
						// + w.getEffect().getRef());
						isLinked = true;
					}
					linkedEdges.add(w.getEffect().getRef());
					// Measure edge quality here

					double nEdgeErrors = 0;
					int nEdgeTimestampErrors = errorDetector
							.edgeTimestampErrorDetector(contextWfURI, w);
					nEdgeErrors += nEdgeTimestampErrors;
					edgeQScores.put(util.createCausalRelationshipIDs(w
							.getCause().getRef(), w.getEffect().getRef()),
							((nEdgeErrors / -EXP_CONST) + EXP_UPPER_BOUND));
					nOutEdges++;
				}
				if (w.getEffect().getRef().equals(artifactID)) {
					// Measure edge quality here

					double nEdgeErrors = 0;
					int nEdgeTimestampErrors = errorDetector
							.edgeTimestampErrorDetector(contextWfURI, w);
					nEdgeErrors += nEdgeTimestampErrors;
					edgeQScores.put(util.createCausalRelationshipIDs(w
							.getCause().getRef(), w.getEffect().getRef()),
							((nEdgeErrors / -EXP_CONST) + EXP_UPPER_BOUND));
					nInEdges++;
				}
			}

			for (WasDerivedFrom w : wasDerivedFrom) {
				if (w.getCause().getRef().equals(artifactID)) {
					String effect = w.getEffect().getRef();
					if (visitedArtifacts.get(effect) == null) {
						if (!q.contains(effect)) {
							q.add(effect);
						}

					} else {
						// System.out.println("\tVisited artifact? "
						// + w.getEffect().getRef());
						isLinked = true;
					}

					linkedEdges.add(w.getEffect().getRef());
					// Measure edge quality here

					double nEdgeErrors = 0;
					int nEdgeTimestampErrors = errorDetector
							.edgeTimestampErrorDetector(contextWfURI, w);
					nEdgeErrors += nEdgeTimestampErrors;
					edgeQScores.put(util.createCausalRelationshipIDs(w
							.getCause().getRef(), w.getEffect().getRef()),
							((nEdgeErrors / -EXP_CONST) + EXP_UPPER_BOUND));
					nOutEdges++;
				}
				if (w.getEffect().getRef().equals(artifactID)) {
					// Measure edge quality here

					double nEdgeErrors = 0;
					int nEdgeTimestampErrors = errorDetector
							.edgeTimestampErrorDetector(contextWfURI, w);
					nEdgeErrors += nEdgeTimestampErrors;
					edgeQScores.put(util.createCausalRelationshipIDs(w
							.getCause().getRef(), w.getEffect().getRef()),
							((nEdgeErrors / -EXP_CONST) + EXP_UPPER_BOUND));
					nInEdges++;
				}
			}

			for (WasGeneratedBy w : wasGeneratedBy) {
				if (w.getEffect().getRef().equals(artifactID)) {
					// Measure edge quality here

					double nEdgeErrors = 0;
					int nEdgeTimestampErrors = errorDetector
							.edgeTimestampErrorDetector(contextWfURI, w);
					nEdgeErrors += nEdgeTimestampErrors;
					edgeQScores.put(util.createCausalRelationshipIDs(w
							.getCause().getRef(), w.getEffect().getRef()),
							((nEdgeErrors / -EXP_CONST) + EXP_UPPER_BOUND));
					nInEdges++;
				}
			}

			if (aConfig != null) {
				int expectedInEdges = Integer.parseInt(aConfig[0]);
				int expectedOutEdges = Integer.parseInt(aConfig[1]);

				if (expectedInEdges != nInEdges) {

					// System.out.println("\tMissing in-edge(s) for process: "
					// + artifactID + ". Expected number of in-edge(s): "
					// + expectedInEdges + ". Actual: " + nInEdges);
				}

				if (expectedOutEdges != nOutEdges) {

					// System.out.println("\tMissing out-edge(s) for artifacts: "
					// + artifactID + ". Expected number of out-edge(s): "
					// + expectedOutEdges + ". Actual: " + nOutEdges);
					//
					// Object[] pKeys = processes.keySet().toArray();
					// Object[] pValues = processes.values().toArray();
					// Object[] aKeys = artifacts.keySet().toArray();
					// Object[] aValues = artifacts.values().toArray();
					// for (int i = 0; i < nExpectedEdges; i++) {
					//
					// if ((artifacts.get(artifactID))
					// .equals(edgesConfig[i][0])) {
					//
					// for (int j = 0; j < pKeys.length; j++) {
					// if (pValues[j].equals(edgesConfig[i][1])
					// && !linkedEdges.contains(pKeys[j])) {
					// // outCandidates.add(pKeys[j].toString());
					// // System.out.println("##" + pKeys[j]);
					// }
					// }
					//
					// for (int j = 0; j < aKeys.length; j++) {
					// if (aValues[j].equals(edgesConfig[i][1])
					// && !linkedEdges.contains(aKeys[j])) {
					// // outCandidates.add(aKeys[j].toString());
					// // System.out.println("##" + aKeys[j]);
					//
					// }
					// }
					// }
					// }
					// GraphAnnotator ga = new GraphAnnotator();
					// ga.artifactAnnotator(artifactID,
					// (expectedOutEdges - nOutEdges), outCandidates,
					// opmGraph, false);

				} else {
					System.out.println("\tExpected number of out-edge(s) for "
							+ artifactID + " detected: " + nOutEdges);
				}

				nErrors = (expectedInEdges - nInEdges)
						+ (expectedOutEdges - nOutEdges);

				nodeQScores.put(artifactID,
						((nErrors / -EXP_CONST) + EXP_UPPER_BOUND));
			}
		}

		return isLinked;
	}

	private boolean agentTraversal(String agentID, OPMGraph opmGraph,
			String contextWfURI) {

		int nOutEdges = 0;
		int nInEdges = 0;
		int nErrors = 0;
		boolean isLinked = false;

		CommonUtil util = new CommonUtil();
		Vector<String> linkedEdges = new Vector<String>();
		Vector<String> childProcesses = new Vector<String>();
		String[] aConfig = agentsConfig.get(agents.get(agentID));
		ErrorDetector errorDetector = new ErrorDetector();
		Agents opmAgents = opmGraph.getAgents();
		WasControlledBy[] wasControlledBy = opmGraph.getCausalDependencies()
				.getWasControlledByArray();

		if (currentRunVisitedAgents.get(agentID) == null) {

			currentRunVisitedAgents.put(agentID, agentID);

			Agent[] agentArray = opmAgents.getAgentArray();
			for (Agent a : agentArray) {
				if (a.getId().equals(agentID)) {
					nErrors += errorDetector.annotationAnalyzer(contextWfURI,
							agentID, Agent.class.getSimpleName(),
							a.getAnnotationArray(), annotationsHash);
				}
			}

			for (WasControlledBy w : wasControlledBy) {
				if (w.getCause().getRef().equals(agentID)) {
					String effect = w.getEffect().getRef();
					if (visitedArtifacts.get(effect) == null) {
						if (!q.contains(effect)) {
							q.add(effect);
						}

					} else {
						// System.out.println("\tVisited artifact? "
						// + w.getEffect().getRef());
						isLinked = true;
					}

					linkedEdges.add(w.getEffect().getRef());
					// Measure edge quality here

					double nEdgeErrors = 0;
					int nEdgeTimestampErrors = errorDetector
							.edgeTimestampErrorDetector(contextWfURI, w);
					nEdgeErrors += nEdgeTimestampErrors;
					edgeQScores.put(util.createCausalRelationshipIDs(w
							.getCause().getRef(), w.getEffect().getRef()),
							((nEdgeErrors / -EXP_CONST) + EXP_UPPER_BOUND));
					nOutEdges++;
				}
				if (w.getEffect().getRef().equals(agentID)) {
					// Measure edge quality here

					double nEdgeErrors = 0;
					int nEdgeTimestampErrors = errorDetector
							.edgeTimestampErrorDetector(contextWfURI, w);
					nEdgeErrors += nEdgeTimestampErrors;
					edgeQScores.put(util.createCausalRelationshipIDs(w
							.getCause().getRef(), w.getEffect().getRef()),
							((nEdgeErrors / -EXP_CONST) + EXP_UPPER_BOUND));
					nInEdges++;
				}
			}

			if (aConfig != null) {
				int expectedInEdges = Integer.parseInt(aConfig[0]);
				int expectedOutEdges = Integer.parseInt(aConfig[1]);

				if (expectedInEdges != nInEdges) {

					// System.out.println("\tMissing in-edge(s) for process: "
					// + artifactID + ". Expected number of in-edge(s): "
					// + expectedInEdges + ". Actual: " + nInEdges);
				}

				if (expectedOutEdges != nOutEdges) {

					// System.out.println("\tMissing out-edge(s) for artifacts: "
					// + artifactID + ". Expected number of out-edge(s): "
					// + expectedOutEdges + ". Actual: " + nOutEdges);
					//
					// Object[] pKeys = processes.keySet().toArray();
					// Object[] pValues = processes.values().toArray();
					// Object[] aKeys = artifacts.keySet().toArray();
					// Object[] aValues = artifacts.values().toArray();
					// for (int i = 0; i < nExpectedEdges; i++) {
					//
					// if ((artifacts.get(artifactID))
					// .equals(edgesConfig[i][0])) {
					//
					// for (int j = 0; j < pKeys.length; j++) {
					// if (pValues[j].equals(edgesConfig[i][1])
					// && !linkedEdges.contains(pKeys[j])) {
					// // outCandidates.add(pKeys[j].toString());
					// // System.out.println("##" + pKeys[j]);
					// }
					// }
					//
					// for (int j = 0; j < aKeys.length; j++) {
					// if (aValues[j].equals(edgesConfig[i][1])
					// && !linkedEdges.contains(aKeys[j])) {
					// // outCandidates.add(aKeys[j].toString());
					// // System.out.println("##" + aKeys[j]);
					//
					// }
					// }
					// }
					// }
					// GraphAnnotator ga = new GraphAnnotator();
					// ga.artifactAnnotator(artifactID,
					// (expectedOutEdges - nOutEdges), outCandidates,
					// opmGraph, false);

				} else {
					System.out.println("\tExpected number of out-edge(s) for "
							+ agentID + " detected: " + nOutEdges);
				}

				nErrors = (expectedInEdges - nInEdges)
						+ (expectedOutEdges - nOutEdges);

				nodeQScores.put(agentID,
						((nErrors / -EXP_CONST) + EXP_UPPER_BOUND));
			}
		}

		return isLinked;
	}

	private double processVisitor(String processID, OPMGraph opmGraph,
			boolean useFix, String contextWfURI) {

		int nOutEdges = 0;
		int nInEdges = 0;
		int nErrors = 0;

		CommonUtil util = new CommonUtil();

		// int nCurrentProcessAncestors = lookupAncestors.get(processID);
		Vector<String> linkedInEdges = new Vector<String>();
		Vector<String> linkedOutEdges = new Vector<String>();
		Vector<String> childArtifacts = new Vector<String>();
		String[] pConfig = processesConfig.get(processes.get(processID));

		Vector<String> tmpVector = new Vector<String>();
		ErrorDetector errorDetector = new ErrorDetector();
		Processes opmProcesses = opmGraph.getProcesses();
		WasGeneratedBy[] wasGeneratedBy = opmGraph.getCausalDependencies()
				.getWasGeneratedByArray();
		WasTriggeredBy[] wasTriggeredBy = opmGraph.getCausalDependencies()
				.getWasTriggeredByArray();
		Used[] used = opmGraph.getCausalDependencies().getUsedArray();

		Process[] processArray = opmProcesses.getProcessArray();

		for (Process p : processArray) {
			if (p.getId().equals(processID)) {
				nErrors += errorDetector.annotationAnalyzer(contextWfURI,
						processID, Process.class.getSimpleName(),
						p.getAnnotationArray(), annotationsHash);

			}
		}

		for (WasGeneratedBy w : wasGeneratedBy) {
			if (w.getCause().getRef().equals(processID)) {
				String effect = w.getEffect().getRef();
				if (!q2.contains(effect)) {
					tmpVector.add(effect);
				}
				childArtifacts.add(effect);

				// int currentArtifactAncestors = nCurrentProcessAncestors + 1;
				// Integer ancestryVal = lookupAncestors.get(effect);
				// if (ancestryVal != null) {
				// if (ancestryVal < currentArtifactAncestors) {
				// lookupAncestors.put(effect, currentArtifactAncestors);
				// }
				// } else {
				// lookupAncestors.put(effect, currentArtifactAncestors);
				//
				// }
				nErrors += errorDetector.annotationAnalyzer(contextWfURI, util
						.createCausalRelationshipIDs(w.getCause().getRef(), w
								.getEffect().getRef()), WasGeneratedBy.class
						.getSimpleName(), w.getAnnotationArray(),
						annotationsHash);
				linkedOutEdges.add(w.getEffect().getRef());

				nOutEdges++;
			}
			if (w.getEffect().getRef().equals(processID)) {
				linkedInEdges.add(w.getCause().getRef());
				nInEdges++;
			}
		}

		for (Used u : used) {
			if (u.getEffect().getRef().equals(processID)) {
				nErrors += errorDetector.annotationAnalyzer(contextWfURI, util
						.createCausalRelationshipIDs(u.getCause().getRef(), u
								.getEffect().getRef()), Used.class
						.getSimpleName(), u.getAnnotationArray(),
						annotationsHash);
				linkedInEdges.add(u.getCause().getRef());
				nInEdges++;
			}
		}

		for (WasTriggeredBy w : wasTriggeredBy) {
			if (w.getCause().getRef().equals(processID)) {
				String effect = w.getEffect().getRef();
				if (!q2.contains(effect)) {
					tmpVector.add(effect);
				}

				// int currentProcessAncestors = nCurrentProcessAncestors + 1;
				// Integer ancestryVal = lookupAncestors.get(effect);
				// if (ancestryVal != null) {
				// if (ancestryVal < currentProcessAncestors) {
				// lookupAncestors.put(effect, currentProcessAncestors);
				// }
				// } else {
				// lookupAncestors.put(effect, currentProcessAncestors);
				// }

				for (Used u : used) {

					String childProcess = u.getEffect().getRef();
					String childArtifact = u.getCause().getRef();
					if (childProcess.equals(effect)
							&& childArtifacts.contains(childArtifact)) {

						// ancestryVal = lookupAncestors.get(effect);
						// if (ancestryVal != 0) {
						// if (ancestryVal <= currentProcessAncestors) {
						// lookupAncestors.put(childProcess,
						// currentProcessAncestors + 1);
						// }
						// } else {
						// lookupAncestors.put(effect,
						// currentProcessAncestors + 1);
						// }

						break;
					}
				}

				nErrors += errorDetector.annotationAnalyzer(contextWfURI, util
						.createCausalRelationshipIDs(w.getCause().getRef(), w
								.getEffect().getRef()), WasTriggeredBy.class
						.getSimpleName(), w.getAnnotationArray(),
						annotationsHash);
				linkedOutEdges.add(w.getEffect().getRef());
				nOutEdges++;

			}

			if (w.getEffect().getRef().equals(processID)) {
				linkedInEdges.add(w.getCause().getRef());
				nErrors += errorDetector.annotationAnalyzer(contextWfURI, util
						.createCausalRelationshipIDs(w.getCause().getRef(), w
								.getEffect().getRef()), WasTriggeredBy.class
						.getSimpleName(), w.getAnnotationArray(),
						annotationsHash);
				nInEdges++;
			}
		}

		if (pConfig != null && useFix) {
			int expectedOutEdges = Integer.parseInt(pConfig[1]);
			int expectedInEdges = Integer.parseInt(pConfig[0]);

			if (expectedInEdges != nInEdges) {
				System.out.println("\tMissing in-edge(s) for process: "
						+ processID + ". Expected number of in-edge(s): "
						+ expectedInEdges + ". Actual: " + nInEdges);

				Object[] pKeys = processes.keySet().toArray();
				Object[] pValues = processes.values().toArray();
				Object[] aKeys = artifacts.keySet().toArray();
				Object[] aValues = artifacts.values().toArray();

				for (int i = 0; i < nExpectedEdges; i++) {

					if ((processes.get(processID)).equals(edgesConfig[i][1])) {

						for (int j = 0; j < pKeys.length; j++) {

							if (pValues[j].equals(edgesConfig[i][0])
									&& !linkedInEdges.contains(pKeys[j])) {

								System.out.println("##missing wasTriggeredBy "
										+ pKeys[j]);

								WasTriggeredBy w = opmGraph
										.getCausalDependencies()
										.addNewWasTriggeredBy();

								w.addNewCause().setRef(pKeys[j].toString());
								w.addNewEffect().setRef(processID);
								OTime oTime = w.addNewTime();
								Calendar[] timeRange = findBestTimeRange(
										pKeys[j].toString(), processID,
										opmGraph);
								if (timeRange[0] != null)
									oTime.setNoEarlierThan(timeRange[0]);
								if (timeRange[1] != null)
									oTime.setNoLaterThan(timeRange[1]);

								Property newProperty = w.addNewAnnotation()
										.addNewProperty();
								newProperty.setUri("inferred");
								try {
									newProperty.setValue(XmlObject.Factory
											.parse("<isInferred>" + true
													+ "</isInferred>"));
								} catch (XmlException e) {
									e.printStackTrace();
								}

								System.out.println("\t" + w);
							}

						}

						for (int j = 0; j < aKeys.length; j++) {
							if (aValues[j].equals(edgesConfig[i][0])
									&& !linkedInEdges.contains(aKeys[j])) {

								System.out
										.println("##missing used " + aKeys[j]);

								Used u = opmGraph.getCausalDependencies()
										.addNewUsed();

								u.addNewCause().setRef(aKeys[j].toString());
								u.addNewEffect().setRef(processID);
								OTime oTime = u.addNewTime();
								Calendar[] timeRange = findBestTimeRange(
										aKeys[j].toString(), processID,
										opmGraph);
								u.addNewRole().setValue("Input");
								if (timeRange[0] != null)
									oTime.setNoEarlierThan(timeRange[0]);
								if (timeRange[1] != null)
									oTime.setNoLaterThan(timeRange[1]);

								Property newProperty = u.addNewAnnotation()
										.addNewProperty();
								newProperty.setUri("inferred");
								try {
									newProperty.setValue(XmlObject.Factory
											.parse("<isInferred>" + true
													+ "</isInferred>"));
								} catch (XmlException e) {
									e.printStackTrace();
								}

								System.out.println("\t" + u);
							}
						}

						if (!artifacts.containsValue(edgesConfig[i][0])
								&& !processes.containsValue(edgesConfig[i][0])) {
							System.err.println(edgesConfig[i][0]
									+ " "
									+ processesConfig
											.containsKey(edgesConfig[i][0]));
							if (artifactsConfig.containsKey(edgesConfig[i][0])) {
								Artifact a = opmGraph.getArtifacts()
										.addNewArtifact();
								a.setId("File_i" + counter);
								counter++;
								// add artifact into artifacts list
								artifacts.put(a.getId(), edgesConfig[i][0]);

								Used u = opmGraph.getCausalDependencies()
										.addNewUsed();

								u.addNewCause().setRef(a.getId());
								u.addNewEffect().setRef(processID);
								OTime oTime = u.addNewTime();
								Calendar[] timeRange = findBestTimeRange(
										a.getId(), processID, opmGraph);
								u.addNewRole().setValue("Input");
								if (timeRange[0] != null)
									oTime.setNoEarlierThan(timeRange[0]);
								if (timeRange[1] != null)
									oTime.setNoLaterThan(timeRange[1]);

								Property newProperty = u.addNewAnnotation()
										.addNewProperty();
								newProperty.setUri("inferred");
								try {
									newProperty.setValue(XmlObject.Factory
											.parse("<isInferred>" + true
													+ "</isInferred>"));
								} catch (XmlException e) {
									e.printStackTrace();
								}

								System.out.println("Missing In-artifact: "
										+ edgesConfig[i][0]);
								if (!q2.contains(a.getId())) {
									tmpVector.add(a.getId());
								}
							} else if (processesConfig
									.containsKey(edgesConfig[i][0])) {
								Process p = opmGraph.getProcesses()
										.addNewProcess();
								p.setId("Process_i" + counter);
								counter++;
								processes.put(p.getId(), edgesConfig[i][0]);

								WasTriggeredBy w = opmGraph
										.getCausalDependencies()
										.addNewWasTriggeredBy();

								w.addNewCause().setRef(p.getId());
								w.addNewEffect().setRef(processID);
								OTime oTime = w.addNewTime();
								Calendar[] timeRange = findBestTimeRange(
										p.getId(), processID, opmGraph);
								if (timeRange[0] != null)
									oTime.setNoEarlierThan(timeRange[0]);
								if (timeRange[1] != null)
									oTime.setNoLaterThan(timeRange[1]);

								Property newProperty = w.addNewAnnotation()
										.addNewProperty();
								newProperty.setUri("inferred");
								try {
									newProperty.setValue(XmlObject.Factory
											.parse("<isInferred>" + true
													+ "</isInferred>"));
								} catch (XmlException e) {
									e.printStackTrace();
								}

								System.out.println("Missing In-process: "
										+ edgesConfig[i][0]);
								if (!q2.contains(p.getId())) {
									tmpVector.add(p.getId());
								}
							}
						}
					}
				}
			}

			if (expectedOutEdges != nOutEdges) {
				System.out.println("\tMissing out-edge(s) for process: "
						+ processID + ". Expected number of out-edge(s): "
						+ expectedOutEdges + ". Actual: " + nOutEdges);

				Object[] pKeys = processes.keySet().toArray();
				Object[] pValues = processes.values().toArray();
				Object[] aKeys = artifacts.keySet().toArray();
				Object[] aValues = artifacts.values().toArray();
				for (int i = 0; i < nExpectedEdges; i++) {

					if ((processes.get(processID)).equals(edgesConfig[i][0])) {
						for (int j = 0; j < pKeys.length; j++) {
							if (pValues[j].equals(edgesConfig[i][1])
									&& !linkedOutEdges.contains(pKeys[j])) {
								// outCandidates.add(pKeys[j].toString());
								System.out.println("##missing wasTriggeredBy"
										+ pKeys[j]);
								WasTriggeredBy w = opmGraph
										.getCausalDependencies()
										.addNewWasTriggeredBy();

								w.addNewCause().setRef(processID);
								w.addNewEffect().setRef(pKeys[j].toString());
								Property newProperty = w.addNewAnnotation()
										.addNewProperty();
								newProperty.setUri("inferred");
								OTime oTime = w.addNewTime();
								Calendar[] timeRange = findBestTimeRange(
										processID, pKeys[j].toString(),
										opmGraph);
								if (timeRange[0] != null)
									oTime.setNoEarlierThan(timeRange[0]);
								if (timeRange[1] != null)
									oTime.setNoLaterThan(timeRange[1]);
								try {
									newProperty.setValue(XmlObject.Factory
											.parse("<isInferred>" + true
													+ "</isInferred>"));
								} catch (XmlException e) {
									e.printStackTrace();
								}
								System.out.println("##::" + w);
							}
						}

						for (int j = 0; j < aKeys.length; j++) {
							if (aValues[j].equals(edgesConfig[i][1])
									&& !linkedOutEdges.contains(aKeys[j])) {
								// outCandidates.add(aKeys[j].toString());
								System.out.println("##missing wasGeneratedBy"
										+ aKeys[j]);
								WasGeneratedBy w = opmGraph
										.getCausalDependencies()
										.addNewWasGeneratedBy();

								w.addNewCause().setRef(processID);
								w.addNewEffect().setRef(aKeys[j].toString());
								w.addNewRole().setValue("Output");
								OTime oTime = w.addNewTime();
								Calendar[] timeRange = findBestTimeRange(
										processID, aKeys[j].toString(),
										opmGraph);
								if (timeRange[0] != null)
									oTime.setNoEarlierThan(timeRange[0]);
								if (timeRange[1] != null)
									oTime.setNoLaterThan(timeRange[1]);

								Property newProperty = w.addNewAnnotation()
										.addNewProperty();
								newProperty.setUri("inferred");
								try {
									newProperty.setValue(XmlObject.Factory
											.parse("<isInferred>" + true
													+ "</isInferred>"));
								} catch (XmlException e) {
									e.printStackTrace();
								}
							}

						}

						if (!artifacts.containsValue(edgesConfig[i][1])
								&& !processes.containsValue(edgesConfig[i][1])) {

							if (artifactsConfig.containsKey(edgesConfig[i][1])) {
								Artifact a = opmGraph.getArtifacts()
										.addNewArtifact();
								a.setId("File_i" + counter);
								counter++;
								// add artifact into artifacts list
								artifacts.put(a.getId(), edgesConfig[i][1]);

								WasGeneratedBy w = opmGraph
										.getCausalDependencies()
										.addNewWasGeneratedBy();

								w.addNewCause().setRef(processID);
								w.addNewEffect().setRef(a.getId());
								OTime oTime = w.addNewTime();
								Calendar[] timeRange = findBestTimeRange(
										a.getId(), processID, opmGraph);
								w.addNewRole().setValue("Output");
								if (timeRange[0] != null)
									oTime.setNoEarlierThan(timeRange[0]);
								if (timeRange[1] != null)
									oTime.setNoLaterThan(timeRange[1]);

								Property newProperty = w.addNewAnnotation()
										.addNewProperty();
								newProperty.setUri("inferred");
								try {
									newProperty.setValue(XmlObject.Factory
											.parse("<isInferred>" + true
													+ "</isInferred>"));
								} catch (XmlException e) {
									e.printStackTrace();
								}

								System.out.println("Missing Out-artifact: "
										+ edgesConfig[i][1]);
								if (!q2.contains(a.getId())) {
									tmpVector.add(a.getId());
								}
							} else if (processesConfig
									.containsKey(edgesConfig[i][1])) {
								Process p = opmGraph.getProcesses()
										.addNewProcess();
								p.setId("Process_i" + counter);
								counter++;
								processes.put(p.getId(), edgesConfig[i][1]);

								WasTriggeredBy w = opmGraph
										.getCausalDependencies()
										.addNewWasTriggeredBy();

								w.addNewCause().setRef(processID);
								w.addNewEffect().setRef(p.getId());
								OTime oTime = w.addNewTime();
								Calendar[] timeRange = findBestTimeRange(
										p.getId(), processID, opmGraph);
								if (timeRange[0] != null)
									oTime.setNoEarlierThan(timeRange[0]);
								if (timeRange[1] != null)
									oTime.setNoLaterThan(timeRange[1]);

								Property newProperty = w.addNewAnnotation()
										.addNewProperty();
								newProperty.setUri("inferred");
								try {
									newProperty.setValue(XmlObject.Factory
											.parse("<isInferred>" + true
													+ "</isInferred>"));
								} catch (XmlException e) {
									e.printStackTrace();
								}

								System.out.println("Missing Out-process: "
										+ edgesConfig[i][1]);
								if (!q2.contains(p.getId())) {
									tmpVector.add(p.getId());
								}
							}

						}
					}
				}

				// GraphAnnotator ga = new GraphAnnotator();
				// ga.processAnnotator(processID, (expectedOutEdges -
				// nOutEdges),
				// outCandidates, opmGraph, true);

			} else {

			}

			nErrors += (expectedInEdges - nInEdges)
					+ (expectedOutEdges - nOutEdges);

			nodeQScores.put(processID,
					((nErrors / -EXP_CONST) + EXP_UPPER_BOUND));
		}

		for (Object o : tmpVector.toArray()) {
			if (o.toString().startsWith("File")
					|| o.toString().startsWith("Block")) {
				if (!q2.contains(o))
					q2.add((String) o);
				tmpVector.remove(o);
			}
		}
		for (Object o : tmpVector.toArray()) {
			if (!q2.contains(o))
				q2.add((String) o);
		}

		return nErrors;
	}

	private double artifactVisitor(String artifactID, OPMGraph opmGraph,
			boolean useFix, String contextWfURI) {

		int nErrors = 0;
		int nOutEdges = 0;
		int nInEdges = 0;

		CommonUtil util = new CommonUtil();
		// int nCurrentArtifactAncestors = lookupAncestors.get(artifactID);
		Vector<String> linkedInEdges = new Vector<String>();
		Vector<String> linkedOutEdges = new Vector<String>();
		Vector<String> childProcesses = new Vector<String>();
		Vector<String> tmpVector = new Vector<String>();
		String[] aConfig = artifactsConfig.get(artifacts.get(artifactID));
		ErrorDetector errorDetector = new ErrorDetector();
		Artifacts opmArtifacts = opmGraph.getArtifacts();
		Used[] used = opmGraph.getCausalDependencies().getUsedArray();
		WasDerivedFrom[] wasDerivedFrom = opmGraph.getCausalDependencies()
				.getWasDerivedFromArray();
		WasGeneratedBy[] wasGeneratedBy = opmGraph.getCausalDependencies()
				.getWasGeneratedByArray();

		Artifact[] artifactArray = opmArtifacts.getArtifactArray();

		for (Artifact a : artifactArray) {
			if (a.getId().equals(artifactID)) {
				nErrors += errorDetector.annotationAnalyzer(contextWfURI,
						artifactID, Artifact.class.getSimpleName(),
						a.getAnnotationArray(), annotationsHash);
			}
		}

		for (Used u : used) {
			if (u.getCause().getRef().equals(artifactID)) {
				String effect = u.getEffect().getRef();
				if (!q2.contains(effect)) {
					tmpVector.add(effect);
				}

				childProcesses.add(effect);

				// int currentProcessAncestors = nCurrentArtifactAncestors + 1;
				Integer ancestryVal = lookupAncestors.get(effect);
				// if (ancestryVal != null) {
				// if (ancestryVal < currentProcessAncestors) {
				// lookupAncestors.put(effect, currentProcessAncestors);
				// }
				// } else {
				// lookupAncestors.put(effect, currentProcessAncestors);
				//
				// }
				nErrors += errorDetector.annotationAnalyzer(contextWfURI, util
						.createCausalRelationshipIDs(u.getCause().getRef(), u
								.getEffect().getRef()), Used.class
						.getSimpleName(), u.getAnnotationArray(),
						annotationsHash);
				linkedOutEdges.add(u.getEffect().getRef());
				nOutEdges++;
			}
			if (u.getEffect().getRef().equals(artifactID)) {
				nErrors += errorDetector.annotationAnalyzer(contextWfURI, util
						.createCausalRelationshipIDs(u.getCause().getRef(), u
								.getEffect().getRef()), Used.class
						.getSimpleName(), u.getAnnotationArray(),
						annotationsHash);
				linkedInEdges.add(u.getCause().getRef());
				nInEdges++;
			}
		}

		for (WasDerivedFrom w : wasDerivedFrom) {
			if (w.getCause().getRef().equals(artifactID)) {
				String effect = w.getEffect().getRef();
				if (!q2.contains(effect)) {
					tmpVector.add(effect);
				}

				// int currentArtifactAncestors = nCurrentArtifactAncestors + 1;

				Integer ancestryVal = lookupAncestors.get(effect);
				// if (ancestryVal != null) {
				// if (ancestryVal < currentArtifactAncestors) {
				// lookupAncestors.put(effect, currentArtifactAncestors);
				// }
				// } else {
				// lookupAncestors.put(effect, currentArtifactAncestors);
				// }
				//
				// for (WasGeneratedBy w1 : wasGeneratedBy) {
				// String childArtifact = w1.getEffect().getRef();
				// String childProcess = w1.getCause().getRef();
				//
				// if (childArtifact.equals(artifactID)
				// && childProcesses.contains(childProcess)) {
				// ancestryVal = lookupAncestors.get(effect);
				// if (ancestryVal != 0) {
				// if (ancestryVal <= currentArtifactAncestors) {
				// lookupAncestors.put(effect,
				// currentArtifactAncestors + 1);
				// } else {
				// lookupAncestors.put(effect,
				// currentArtifactAncestors + 1);
				// }
				// }
				// break;
				// }
				// }
				nErrors += errorDetector.annotationAnalyzer(contextWfURI, util
						.createCausalRelationshipIDs(w.getCause().getRef(), w
								.getEffect().getRef()), WasDerivedFrom.class
						.getSimpleName(), w.getAnnotationArray(),
						annotationsHash);
				linkedOutEdges.add(w.getEffect().getRef());
				nOutEdges++;
			}
			if (w.getEffect().getRef().equals(artifactID)) {
				linkedInEdges.add(w.getCause().getRef());
				nInEdges++;
			}
		}

		for (WasGeneratedBy w : wasGeneratedBy) {
			if (w.getEffect().getRef().equals(artifactID)) {
				nErrors += errorDetector.annotationAnalyzer(contextWfURI, util
						.createCausalRelationshipIDs(w.getCause().getRef(), w
								.getEffect().getRef()), WasGeneratedBy.class
						.getSimpleName(), w.getAnnotationArray(),
						annotationsHash);
				linkedInEdges.add(w.getCause().getRef());
				nInEdges++;
			}
		}

		if (aConfig != null && useFix) {
			int expectedInEdges = Integer.parseInt(aConfig[0]);
			int expectedOutEdges = Integer.parseInt(aConfig[1]);

			if (expectedInEdges != nInEdges) {
				System.out.println("\tMissing in-edge(s) for artifact: "
						+ artifactID + ". Expected number of in-edge(s): "
						+ expectedInEdges + ". Actual: " + nInEdges);
				for (int i = 0; i < nInEdges; i++) {
					System.out.println(linkedInEdges.get(i));
				}

				Object[] pKeys = processes.keySet().toArray();
				Object[] pValues = processes.values().toArray();
				Object[] aKeys = artifacts.keySet().toArray();
				Object[] aValues = artifacts.values().toArray();
				for (int i = 0; i < nExpectedEdges; i++) {

					if ((artifacts.get(artifactID)).equals(edgesConfig[i][1])) {
						for (int j = 0; j < pKeys.length; j++) {
							if (pValues[j].equals(edgesConfig[i][0])
									&& !linkedInEdges.contains(pKeys[j])) {
								System.out.println("##missing wasGeneratedBy"
										+ pKeys[j] + " " + nExpectedEdges);

								WasGeneratedBy w = opmGraph
										.getCausalDependencies()
										.addNewWasGeneratedBy();

								w.addNewCause().setRef(pKeys[j].toString());
								w.addNewEffect().setRef(artifactID);
								w.addNewRole().setValue("Output");
								OTime oTime = w.addNewTime();
								Calendar[] timeRange = findBestTimeRange(
										artifactID, pKeys[j].toString(),
										opmGraph);
								if (timeRange[0] != null)
									oTime.setNoEarlierThan(timeRange[0]);
								if (timeRange[1] != null)
									oTime.setNoLaterThan(timeRange[1]);

								Property newProperty = w.addNewAnnotation()
										.addNewProperty();
								newProperty.setUri("inferred");
								try {
									newProperty.setValue(XmlObject.Factory
											.parse("<isInferred>" + true
													+ "</isInferred>"));
								} catch (XmlException e) {
									e.printStackTrace();
								}

								System.out.println("\t" + w);
							}
						}

						for (int j = 0; j < aKeys.length; j++) {
							if (aValues[j].equals(edgesConfig[i][0])
									&& !linkedInEdges.contains(aKeys[j])) {

								System.out.println("##missing wasDerivedFrom"
										+ aKeys[j] + " " + nExpectedEdges);

								WasDerivedFrom w = opmGraph
										.getCausalDependencies()
										.addNewWasDerivedFrom();

								w.addNewCause().setRef(aKeys[j].toString());
								w.addNewEffect().setRef(artifactID);
								OTime oTime = w.addNewTime();
								Calendar[] timeRange = findBestTimeRange(
										artifactID, aKeys[j].toString(),
										opmGraph);
								if (timeRange[0] != null)
									oTime.setNoEarlierThan(timeRange[0]);
								if (timeRange[1] != null)
									oTime.setNoLaterThan(timeRange[1]);

								Property newProperty = w.addNewAnnotation()
										.addNewProperty();
								newProperty.setUri("inferred");
								try {
									newProperty.setValue(XmlObject.Factory
											.parse("<isInferred>" + true
													+ "</isInferred>"));
								} catch (XmlException e) {
									e.printStackTrace();
								}

								System.out.println("\t" + w);
							}
						}

						if (!artifacts.containsValue(edgesConfig[i][0])
								&& !processes.containsValue(edgesConfig[i][0])) {

							if (artifactsConfig.containsKey(edgesConfig[i][0])) {
								Artifact a = opmGraph.getArtifacts()
										.addNewArtifact();
								a.setId("File_i" + counter);
								counter++;
								// add artifact into artifacts list
								artifacts.put(a.getId(), edgesConfig[i][0]);

								WasDerivedFrom w = opmGraph
										.getCausalDependencies()
										.addNewWasDerivedFrom();

								w.addNewCause().setRef(a.getId());
								w.addNewEffect().setRef(artifactID);
								OTime oTime = w.addNewTime();
								Calendar[] timeRange = findBestTimeRange(
										a.getId(), artifactID, opmGraph);

								if (timeRange[0] != null)
									oTime.setNoEarlierThan(timeRange[0]);
								if (timeRange[1] != null)
									oTime.setNoLaterThan(timeRange[1]);

								Property newProperty = w.addNewAnnotation()
										.addNewProperty();
								newProperty.setUri("inferred");
								try {
									newProperty.setValue(XmlObject.Factory
											.parse("<isInferred>" + true
													+ "</isInferred>"));
								} catch (XmlException e) {
									e.printStackTrace();
								}

								System.out.println("Missing In-artifact: "
										+ edgesConfig[i][0]);
								if (!q2.contains(a.getId())) {
									tmpVector.add(a.getId());
								}
							} else if (processesConfig
									.containsKey(edgesConfig[i][0])) {
								Process p = opmGraph.getProcesses()
										.addNewProcess();
								p.setId("Process_i" + counter);
								counter++;
								processes.put(p.getId(), edgesConfig[i][0]);

								WasGeneratedBy w = opmGraph
										.getCausalDependencies()
										.addNewWasGeneratedBy();

								w.addNewCause().setRef(p.getId());
								w.addNewEffect().setRef(artifactID);
								w.addNewRole().setValue("Output");
								OTime oTime = w.addNewTime();
								Calendar[] timeRange = findBestTimeRange(
										p.getId(), artifactID, opmGraph);
								if (timeRange[0] != null)
									oTime.setNoEarlierThan(timeRange[0]);
								if (timeRange[1] != null)
									oTime.setNoLaterThan(timeRange[1]);

								Property newProperty = w.addNewAnnotation()
										.addNewProperty();
								newProperty.setUri("inferred");
								try {
									newProperty.setValue(XmlObject.Factory
											.parse("<isInferred>" + true
													+ "</isInferred>"));
								} catch (XmlException e) {
									e.printStackTrace();
								}

								System.out.println("Missing In-process: "
										+ edgesConfig[i][0]);
								if (!q2.contains(p.getId())) {
									tmpVector.add(p.getId());
								}
							}
						}

					}

				}
			}
			if (expectedOutEdges != nOutEdges) {
				// System.out.println("Candidates... for " + artifactID
				// + artifacts.get(artifactID) + ":");

				Object[] pKeys = processes.keySet().toArray();
				Object[] pValues = processes.values().toArray();
				Object[] aKeys = artifacts.keySet().toArray();
				Object[] aValues = artifacts.values().toArray();
				for (int i = 0; i < nExpectedEdges; i++) {

					if ((artifacts.get(artifactID)).equals(edgesConfig[i][0])) {
						for (int j = 0; j < pKeys.length; j++) {
							if (pValues[j].equals(edgesConfig[i][1])
									&& !linkedOutEdges.contains(pKeys[j])) {
								System.out.println("##missing used" + pKeys[j]);
								Used w = opmGraph.getCausalDependencies()
										.addNewUsed();

								w.addNewCause().setRef(artifactID);
								w.addNewEffect().setRef(pKeys[j].toString());
								w.addNewRole().setValue("Input");
								OTime oTime = w.addNewTime();
								Calendar[] timeRange = findBestTimeRange(
										artifactID, pKeys[j].toString(),
										opmGraph);
								if (timeRange[0] != null)
									oTime.setNoEarlierThan(timeRange[0]);
								if (timeRange[1] != null)
									oTime.setNoLaterThan(timeRange[1]);
								Property newProperty = w.addNewAnnotation()
										.addNewProperty();
								newProperty.setUri("inferred");
								try {
									newProperty.setValue(XmlObject.Factory
											.parse("<isInferred>" + true
													+ "</isInferred>"));
								} catch (XmlException e) {
									e.printStackTrace();
								}
								System.out.println("##::" + w);
							}
						}

						for (int j = 0; j < aKeys.length; j++) {
							if (aValues[j].equals(edgesConfig[i][1])
									&& !linkedOutEdges.contains(aKeys[j])) {
								System.out.println("##missing wasDerivedFrom"
										+ aKeys[j]);

								WasDerivedFrom w = opmGraph
										.getCausalDependencies()
										.addNewWasDerivedFrom();

								w.addNewCause().setRef(artifactID);
								w.addNewEffect().setRef(aKeys[j].toString());
								OTime oTime = w.addNewTime();
								Calendar[] timeRange = findBestTimeRange(
										artifactID, aKeys[j].toString(),
										opmGraph);
								if (timeRange[0] != null)
									oTime.setNoEarlierThan(timeRange[0]);
								if (timeRange[1] != null)
									oTime.setNoLaterThan(timeRange[1]);
								Property newProperty = w.addNewAnnotation()
										.addNewProperty();
								newProperty.setUri("inferred");

								try {
									newProperty.setValue(XmlObject.Factory
											.parse("<isInferred>" + true
													+ "</isInferred>"));
								} catch (XmlException e) {
									e.printStackTrace();
								}
								System.out.println("##::" + w);

							}

							if (!artifacts.containsValue(edgesConfig[i][1])
									&& !processes
											.containsValue(edgesConfig[i][1])) {

								if (artifactsConfig
										.containsKey(edgesConfig[i][1])) {
									Artifact a = opmGraph.getArtifacts()
											.addNewArtifact();
									a.setId("File_i" + counter);
									counter++;
									// add artifact into artifacts list
									artifacts.put(a.getId(), edgesConfig[i][1]);

									WasDerivedFrom w = opmGraph
											.getCausalDependencies()
											.addNewWasDerivedFrom();

									w.addNewCause().setRef(artifactID);
									w.addNewEffect().setRef(a.getId());
									OTime oTime = w.addNewTime();
									Calendar[] timeRange = findBestTimeRange(
											a.getId(), artifactID, opmGraph);
									if (timeRange[0] != null)
										oTime.setNoEarlierThan(timeRange[0]);
									if (timeRange[1] != null)
										oTime.setNoLaterThan(timeRange[1]);

									Property newProperty = w.addNewAnnotation()
											.addNewProperty();
									newProperty.setUri("inferred");
									try {
										newProperty.setValue(XmlObject.Factory
												.parse("<isInferred>" + true
														+ "</isInferred>"));
									} catch (XmlException e) {
										e.printStackTrace();
									}

									System.out.println("Missing Out-artifact: "
											+ edgesConfig[i][1]);
									if (!q2.contains(a.getId())) {
										tmpVector.add(a.getId());
									}
								} else if (processesConfig
										.containsKey(edgesConfig[i][1])) {
									Process p = opmGraph.getProcesses()
											.addNewProcess();
									p.setId("Process_i" + counter);
									counter++;
									processes.put(p.getId(), edgesConfig[i][1]);

									Used u = opmGraph.getCausalDependencies()
											.addNewUsed();

									u.addNewCause().setRef(artifactID);
									u.addNewEffect().setRef(p.getId());
									u.addNewRole().setValue("Input");
									OTime oTime = u.addNewTime();
									Calendar[] timeRange = findBestTimeRange(
											p.getId(), artifactID, opmGraph);
									if (timeRange[0] != null)
										oTime.setNoEarlierThan(timeRange[0]);
									if (timeRange[1] != null)
										oTime.setNoLaterThan(timeRange[1]);

									Property newProperty = u.addNewAnnotation()
											.addNewProperty();
									newProperty.setUri("inferred");
									try {
										newProperty.setValue(XmlObject.Factory
												.parse("<isInferred>" + true
														+ "</isInferred>"));
									} catch (XmlException e) {
										e.printStackTrace();
									}

									System.out.println("Missing Out-process: "
											+ edgesConfig[i][1]);
									if (!q2.contains(p.getId())) {
										tmpVector.add(p.getId());
									}
								}

							}
						}
					}
				}
			} else {
			}

			nErrors += (expectedInEdges - nInEdges)
					+ (expectedOutEdges - nOutEdges);

			nodeQScores.put(artifactID,
					((nErrors / -EXP_CONST) + EXP_UPPER_BOUND));
		}

		for (Object o : tmpVector.toArray()) {
			if (o.toString().startsWith("Process_")) {
				if (!q2.contains(o))
					q2.add((String) o);
				tmpVector.remove(o);
			}
		}
		for (Object o : tmpVector.toArray()) {
			if (!q2.contains(o))
				q2.add((String) o);
		}

		return nErrors;
	}
}