/*
 * Author: You-Wei Cheah
 * 
 * This is the file containing main that reads in configuration files 
 * and initiates the graphProcessor.
 */
package graph.extractor;

import graph.analyze.GraphProcessor;

import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.LineNumberReader;
import java.rmi.RemoteException;
import java.util.Vector;

import org.apache.axis2.AxisFault;
import org.apache.xmlbeans.XmlException;
import org.dataandsearch.www.karma._2010._08.KarmaServiceStub;
import org.dataandsearch.www.karma.query._2010._10.DetailEnumType;
import org.dataandsearch.www.karma.query._2010._10.FormatEnumType;
import org.dataandsearch.www.karma.query._2010._10.GetWorkflowGraphRequestDocument;
import org.dataandsearch.www.karma.query._2010._10.GetWorkflowGraphRequestType;
import org.dataandsearch.www.karma.query._2010._10.GetWorkflowGraphResponseDocument;
import org.openprovenance.model.v1_1_a.OpmGraphDocument;

public class GraphExtractor {
	private static boolean verbose = true;

	// Data structures
	private Vector<String> wfs = new Vector<String>();

	private GetWorkflowGraphRequestDocument makeGetWorkflowGraph(
			String contextWfURI) {
		GetWorkflowGraphRequestDocument getWorkflowGraphRequestDocument = GetWorkflowGraphRequestDocument.Factory
				.newInstance();

		GetWorkflowGraphRequestType getWorkflowGraphRequest = getWorkflowGraphRequestDocument
				.addNewGetWorkflowGraphRequest();
		getWorkflowGraphRequest.setWorkflowID(contextWfURI);
		getWorkflowGraphRequest.setFormat(FormatEnumType.OPM);
		getWorkflowGraphRequest.setInformationDetailLevel(DetailEnumType.FINE);

		return getWorkflowGraphRequestDocument;
	}

	public static void printHelp() {
		System.out
				.println("Use: [Karma_service_URI | directory_with_OPM_provenance] " +
						"[output_file_location] [input_file_containing_workflowIDs] " +
						"[context_workflow_URI_prefix (optional)]");
	}

	public static void main(String[] args) {

		if (args.length < 3 || args.length > 4) {
			printHelp();
			return;
		}

		String karmaServiceURI = args[0];
		String outputFile = args[1];
		String wfListConfigFile = args[2];
		String contextWfURIPrefix = ""; // optional argument

		if (args.length > 3) {
			contextWfURIPrefix = args[3];
		}

		if (verbose) {
			System.out.println("Karma service URI: " + karmaServiceURI);
			System.out.println("Output file location: " + outputFile);
			System.out
					.println("Workflow list config file: " + wfListConfigFile);
			System.out.println("Context workflow URI prefix:"
					+ contextWfURIPrefix);
		}

		GraphExtractor ge = new GraphExtractor();
		FileReader fileRead = null;
		FileReader inputRead = null;
		String nextLine = null;

		try {
			fileRead = new FileReader(wfListConfigFile);
			LineNumberReader lineReader = new LineNumberReader(fileRead);

			while ((nextLine = lineReader.readLine()) != null) {
				ge.wfs.add(contextWfURIPrefix + nextLine);
			}

			lineReader.close();
			fileRead.close();
		} catch (FileNotFoundException e) {
			System.err
					.println("Workflow list config file not found exception: "
							+ e.getLocalizedMessage());
		} catch (IOException e) {
			System.err.println("Workflow list config file IO exception: "
					+ e.getLocalizedMessage());
		}

		try {
			FileWriter output = new FileWriter(outputFile);
			KarmaServiceStub stub = new KarmaServiceStub(karmaServiceURI);

			output.write("wfURI\t index \t" + "nVertices\t" + "nEdges\t"
					+ "nSubgraphs\t" + "isFailed?\t" + "originalScore\t"
					+ "newNVertices\t" + "newNEdges\t" + "newNSubgraphs\t"
					+ "newNErrors\t" + "newScore\n");
			output.flush();
			
			int i = 0;

			GraphProcessor processor = new GraphProcessor();

			for (String contextWfURI : ge.wfs) {
				try {
					// if Karma service URI provided
					if (karmaServiceURI.startsWith("http")) {

						GetWorkflowGraphResponseDocument workflowGraph = stub
								.getWorkflowGraph(ge
										.makeGetWorkflowGraph(contextWfURI));

						if (verbose)
							System.err.println("GraphExtractor: "
									+ contextWfURI + "\n\t" + workflowGraph);

						Object[] graphAttributes = processor.graphProcesor(
								stub, contextWfURI, workflowGraph
										.getGetWorkflowGraphResponse()
										.getOpmGraph());

						i += 1;
						// write results to file
						output.write(contextWfURI + "\t" + i + "\t"
								+ String.valueOf(graphAttributes[0]) + "\t"
								+ String.valueOf(graphAttributes[1]) + "\t"
								+ String.valueOf(graphAttributes[2]) + "\t"
								+ String.valueOf(graphAttributes[3]) + "\t"
								+ String.valueOf(graphAttributes[4]) + "\t"
								+ String.valueOf(graphAttributes[5]) + "\t"
								+ String.valueOf(graphAttributes[6]) + "\t"
								+ String.valueOf(graphAttributes[7]) + "\t"
								+ String.valueOf(graphAttributes[8]) + "\t"
								+ String.valueOf(graphAttributes[9]) + "\n");

						output.flush();

					} else {
						inputRead = new FileReader(karmaServiceURI
								+ contextWfURI + ".xml");
						LineNumberReader lineReader = new LineNumberReader(
								inputRead);

						while ((nextLine = lineReader.readLine()) != null) {
							if (nextLine.startsWith("<?xml version")) {
								continue;
							}
							OpmGraphDocument opm = OpmGraphDocument.Factory
									.parse(nextLine);
							Object[] graphAttributes = processor.graphProcesor(
									null, contextWfURI, opm.getOpmGraph());
							
							i += 1;
							// write results to file
							output.write(contextWfURI + "\t" + i + "\t"
									+ String.valueOf(graphAttributes[0]) + "\t"
									+ String.valueOf(graphAttributes[1]) + "\t"
									+ String.valueOf(graphAttributes[2]) + "\t"
									+ String.valueOf(graphAttributes[3]) + "\t"
									+ String.valueOf(graphAttributes[4]) + "\t"
									+ String.valueOf(graphAttributes[5]) + "\t"
									+ String.valueOf(graphAttributes[6]) + "\t"
									+ String.valueOf(graphAttributes[7]) + "\t"
									+ String.valueOf(graphAttributes[8]) + "\t"
									+ String.valueOf(graphAttributes[9]) + "\n");

							output.flush();
						}

						lineReader.close();
						inputRead.close();
					}
				} catch (AxisFault karmaAxisFault) {
					// TODO Auto-generated catch block
					karmaAxisFault.printStackTrace();
				} catch (RemoteException re) {
					// TODO Auto-generated catch block
					re.printStackTrace();
				} catch (XmlException xmle) {
					// TODO Auto-generated catch block
					xmle.printStackTrace();
				}
			}

			processor.printStructuralStats();

			stub.cleanup();
			output.close();

		} catch (IOException e) {
			System.err.println("Output file IO exception: "
					+ e.getLocalizedMessage());
		}
	}
}