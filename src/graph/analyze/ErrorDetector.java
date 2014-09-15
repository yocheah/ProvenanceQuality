package graph.analyze;

import graph.common.CommonUtil;

import java.awt.List;
import java.io.FileWriter;
import java.io.IOException;
import java.text.DecimalFormat;
import java.util.Calendar;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.Vector;

import org.apache.xmlbeans.XmlObject;
import org.dataandsearch.www.karma._2010._08.KarmaServiceStub;
import org.openprovenance.model.v1_1_a.EmbeddedAnnotation;
import org.openprovenance.model.v1_1_a.Property;
import org.openprovenance.model.v1_1_a.Used;
import org.openprovenance.model.v1_1_a.WasControlledBy;
import org.openprovenance.model.v1_1_a.WasDerivedFrom;
import org.openprovenance.model.v1_1_a.WasGeneratedBy;
import org.openprovenance.model.v1_1_a.WasTriggeredBy;
import org.openprovenance.model.v1_1_a.impl.UsedImpl;
import org.openprovenance.model.v1_1_a.impl.WasControlledByImpl;
import org.openprovenance.model.v1_1_a.impl.WasDerivedFromImpl;
import org.openprovenance.model.v1_1_a.impl.WasGeneratedByImpl;
import org.openprovenance.model.v1_1_a.impl.WasTriggeredByImpl;

public class ErrorDetector {

	private static final long WEEK_TIME_IN_MILLIS = 3600000 * 24 * 7;
	private final static String ANNO_STATS_OUTPUT_FILE = "config/output/annoStatsAnalyzer";
	private final static String TIME_ERR_OUTPUT_FILE = "config/output/timeAnalyzer";
	private static final String TEMPORAL_OUTPUT_FILE = "config/output/temporalOutput";
	private static final String TEMPORAL_ANNA_FILE = "config/output/temporalAnalyzer";

	private static boolean isAnnoFileCreated = false;
	private static boolean isTimeFileCreated = false;
	private static HashMap<String, String> preventDuplicatesInProcessing = new HashMap<String, String>();
	private static HashMap<String, Integer> annoStats = new HashMap<String, Integer>();
	private static HashMap<String, HashMap<Integer, Integer>> annoDensityByType = new HashMap<String, HashMap<Integer, Integer>>();
	private static HashMap<String, HashMap<Integer, Integer>> annoDensityByTypeNoDup = new HashMap<String, HashMap<Integer, Integer>>();
	private static HashMap<String, Calendar[]> temporalCache = new HashMap<String, Calendar[]>();

	protected void clearStatic() {
		preventDuplicatesInProcessing.clear();
		annoStats.clear();
		annoDensityByType.clear();
		annoDensityByTypeNoDup.clear();
		temporalCache.clear();
	}
	
	protected int evaluteEarlyLateRelationship(String cwf, String id,
			Calendar earlier, Calendar later) {
		int nErrors = 0;
		try {
			FileWriter timeErrOutput;
			FileWriter temporalOutput;
			if (isTimeFileCreated) {
				timeErrOutput = new FileWriter((TIME_ERR_OUTPUT_FILE
						+ cwf.replace(":", "+").replace("/", "_") + ".txt"),
						true);
				temporalOutput = new FileWriter((TEMPORAL_OUTPUT_FILE
						+ cwf.replace(":", "+").replace("/", "_") + ".txt"),
						true);
			} else {
				timeErrOutput = new FileWriter((TIME_ERR_OUTPUT_FILE
						+ cwf.replace(":", "+").replace("/", "_") + ".txt"));
				temporalOutput = new FileWriter((TEMPORAL_OUTPUT_FILE
						+ cwf.replace(":", "+").replace("/", "_") + ".txt"));
				isTimeFileCreated = true;
			}

			if (later != null && earlier != null) {
				if (earlier.after(later)) {
					timeErrOutput.write("id: " + id + "\tTime is reversed: "
							+ "\tLater: " + later + "\tEarlier: " + earlier
							+ "\n");
					nErrors++;
				}

				if (earlier.getTimeInMillis() < 0) {
					timeErrOutput.write("id: " + id
							+ "\tEarlier time is before UNIX time." + "\n");
				}

				if (later.getTimeInMillis() < 0) {
					timeErrOutput.write("id: " + id
							+ "\tLater time is before UNIX time." + "\n");
				}

				if ((later.getTimeInMillis() - earlier.getTimeInMillis()) > WEEK_TIME_IN_MILLIS) {
					timeErrOutput.write("id: " + id
							+ "\tTime difference is greater than a week: "
							+ earlier + " " + later + "\n");
					nErrors++;
				}

				temporalOutput.write(id + "\t" + earlier.getTimeInMillis()
						+ "\t" + later.getTimeInMillis() + "\t" + earlier
						+ "\t" + later + "\n");
			}

			Calendar[] temporal = new Calendar[2];
			temporal[0] = earlier;
			temporal[1] = later;
			temporalCache.put(id, temporal);

			temporalOutput.flush();
			temporalOutput.close();

			timeErrOutput.flush();
			timeErrOutput.close();

		} catch (Exception e) {
			e.printStackTrace();
		}
		return nErrors;

	}

	protected int annotationAnalyzer(String cwf, String id, String type,
			EmbeddedAnnotation[] annotationArray,
			HashMap<String, String> annotationsHash) {

		EmbeddedAnnotation embeddedAnnotation = EmbeddedAnnotation.Factory
				.newInstance();
		int nErrors = 0;
		int nDuplicates = 0;
		int nAnnos = 0;
		HashMap<String, String> annotations = new HashMap<String, String>();

		// merge all annotation arrays into a single array
		for (EmbeddedAnnotation a : annotationArray) {
			for (Property p : a.getPropertyArray()) {
				Property newProperty = embeddedAnnotation.addNewProperty();
				newProperty.setUri(p.getUri());
				newProperty.setValue(p.getValue());
				nAnnos++;
			}
		}

		Property[] propertyArray = embeddedAnnotation.getPropertyArray();

		for (int i = 0; i < propertyArray.length; i++) {

			String uri = propertyArray[i].getUri();
			XmlObject value = propertyArray[i].getValue();

			annotationsHash.put(uri, "");
			annotations.put(uri, "");

			for (int j = 0; j < propertyArray.length; j++) {
				if (i > j) {
					if (uri.equals(propertyArray[j].getUri())) {
						nDuplicates++;
						XmlObject value2 = propertyArray[j].getValue();
						if (!value.xmlText().equals(value2.xmlText())) {
							System.err
									.println("Potentially conflicting values detected: \n\turi: "
											+ uri
											+ " \n\tvalues:\n\t"
											+ value.xmlText()
											+ "\n\t"
											+ value2.xmlText());
							nErrors++;
						}
						propertyArray[j].setUri(null); // Nullify duplicate keys
														// so that no longer
														// marked as duplicate
					}
				}
			}
		}
		// System.out.println(id + " " + nErrors + " " + nDuplicates + " "
		// + nAnnos);
		try {
			FileWriter annoStatsOutput;
			if (isAnnoFileCreated) {
				annoStatsOutput = new FileWriter(ANNO_STATS_OUTPUT_FILE
						+ cwf.replace(":", "+").replace("/", "_") + ".txt",
						true);
			} else {
				annoStatsOutput = new FileWriter(ANNO_STATS_OUTPUT_FILE
						+ cwf.replace(":", "+").replace("/", "_") + ".txt");
				isAnnoFileCreated = true;
			}

			if (!preventDuplicatesInProcessing.containsKey(id)) {
				annoStatsOutput.append(id + "\t" + type + "\t" + nAnnos + "\t"
						+ annotations.keySet().size() + "\t" + nDuplicates
						+ "\t" + nErrors + "\n");
				preventDuplicatesInProcessing.put(id, id);

				Integer cumulativeAnnos = annoStats.get(type);
				if (cumulativeAnnos != null) {
					annoStats.put(type, cumulativeAnnos + nAnnos);
				} else {
					annoStats.put(type, nAnnos);
				}

				HashMap<Integer, Integer> countByGroup = annoDensityByType
						.get(type);
				HashMap<Integer, Integer> countByGroupNoDup = annoDensityByTypeNoDup
						.get(type);

				if (countByGroup != null) {
					Integer count = countByGroup.get(nAnnos);

					if (count != null) {
						countByGroup.put(nAnnos, ++count);
					} else {
						countByGroup.put(nAnnos, 1);
					}

				} else {
					countByGroup = new HashMap<Integer, Integer>();
					countByGroup.put(nAnnos, 1);
				}

				int nAnnosNoDup = nAnnos - nDuplicates;

				if (countByGroupNoDup != null) {
					Integer count = countByGroupNoDup.get(nAnnosNoDup);

					if (count != null) {
						countByGroupNoDup.put(nAnnosNoDup, ++count);
					} else {
						countByGroupNoDup.put(nAnnosNoDup, 1);
					}

				} else {
					countByGroupNoDup = new HashMap<Integer, Integer>();
					countByGroupNoDup.put(nAnnosNoDup, 1);
				}

				annoDensityByType.put(type, countByGroup);
				annoDensityByTypeNoDup.put(type, countByGroupNoDup);
			}

			annoStatsOutput.flush();
			annoStatsOutput.close();

		} catch (Exception e) {
			e.printStackTrace();
		}

		return nErrors;
	}

	protected int edgeTimestampErrorDetector(String cwf, Object o) {
		String relationshipClassName = o.getClass().getSimpleName();
		int nErrors = 0;
		Calendar earlier = null;
		Calendar later = null;
		CommonUtil util = new CommonUtil();

		if (WasGeneratedByImpl.class.getSimpleName().equals(
				relationshipClassName)) {
			WasGeneratedBy w = (WasGeneratedBy) o;

			if (w.isSetTime()) {
				if (w.getTime().isSetNoEarlierThan()) {
					try {
						earlier = w.getTime().getNoEarlierThan();
						// System.out.println("Earlier: " + earlier);
					} catch (Exception e) {
						System.err.println("Invalid time.");
						nErrors++;
					}
				}

				if (w.getTime().isSetNoLaterThan()) {

					try {
						later = w.getTime().getNoLaterThan();
						// System.out.println("Later: " + later);
					} catch (Exception e) {
						System.err.println("Invalid time.");
						nErrors++;
					}
				}

				if (w.getTime().isSetExactlyAt()) {
					try {
						earlier = w.getTime().getExactlyAt();
						later = w.getTime().getExactlyAt();
					} catch (Exception e) {
						System.err.println("Invalid time.");
						nErrors++;
					}
				}
			}

			nErrors += evaluteEarlyLateRelationship(cwf,
					util.createCausalRelationshipIDs(w.getCause().getRef(), w
							.getEffect().getRef()), earlier, later);

		} else if (UsedImpl.class.getSimpleName().equals(relationshipClassName)) {
			Used u = (Used) o;

			if (u.isSetTime()) {
				if (u.getTime().isSetNoEarlierThan()) {
					try {
						earlier = u.getTime().getNoEarlierThan();
						// System.out.println("Earlier: " + earlier);
					} catch (Exception e) {
						System.err.println("Invalid time.");
						nErrors++;
					}
				}

				if (u.getTime().isSetNoLaterThan()) {

					try {
						later = u.getTime().getNoLaterThan();
						// System.out.println("Later: " + later);
					} catch (Exception e) {
						System.err.println("Invalid time.");
						nErrors++;
					}
				}
			}

			nErrors += evaluteEarlyLateRelationship(cwf,
					util.createCausalRelationshipIDs(u.getCause().getRef(), u
							.getEffect().getRef()), earlier, later);
		} else if (WasDerivedFromImpl.class.getSimpleName().equals(
				relationshipClassName)) {
			WasDerivedFrom w = (WasDerivedFrom) o;

			if (w.isSetTime()) {
				if (w.getTime().isSetNoEarlierThan()) {
					try {
						earlier = w.getTime().getNoEarlierThan();
						// System.out.println("Earlier: " + earlier);
					} catch (Exception e) {
						System.err.println("Invalid time.");
						nErrors++;
					}
				}

				if (w.getTime().isSetNoLaterThan()) {

					try {
						later = w.getTime().getNoLaterThan();
						// System.out.println("Later: " + later);
					} catch (Exception e) {
						System.err.println("Invalid time.");
						nErrors++;
					}
				}
			}

			nErrors += evaluteEarlyLateRelationship(cwf,
					util.createCausalRelationshipIDs(w.getCause().getRef(), w
							.getEffect().getRef()), earlier, later);
		} else if (WasTriggeredByImpl.class.getSimpleName().equals(
				relationshipClassName)) {
			WasTriggeredBy w = (WasTriggeredBy) o;

			if (w.isSetTime()) {
				if (w.getTime().isSetNoEarlierThan()) {
					try {
						earlier = w.getTime().getNoEarlierThan();
						// System.out.println("Earlier: " + earlier);
					} catch (Exception e) {
						System.err.println("Invalid time.");
						nErrors++;
					}
				}

				if (w.getTime().isSetNoLaterThan()) {

					try {
						later = w.getTime().getNoLaterThan();
						// System.out.println("Later: " + later);
					} catch (Exception e) {
						System.err.println("Invalid time.");
						nErrors++;
					}
				}
			}

			nErrors += evaluteEarlyLateRelationship(cwf,
					util.createCausalRelationshipIDs(w.getCause().getRef(), w
							.getEffect().getRef()), earlier, later);
		} else if (WasControlledByImpl.class.getSimpleName().equals(
				relationshipClassName)) {
			WasControlledBy w = (WasControlledBy) o;

			if (w.isSetStartTime()) {
				if (w.getStartTime().isSetNoEarlierThan()) {
					try {
						earlier = w.getStartTime().getNoEarlierThan();
						// System.out.println("Earlier: " + earlier);
					} catch (Exception e) {
						System.err.println("Invalid time.");
						nErrors++;
					}
				}
				if (w.getStartTime().isSetNoLaterThan()) {
					try {
						if (earlier.after(w.getStartTime().getNoEarlierThan())) {
							earlier = w.getStartTime().getNoEarlierThan();
							nErrors++;
						}
						// System.out.println("Later: " + later);
					} catch (Exception e) {
						System.err.println("Invalid time.");
						nErrors++;
					}
				}

				if (w.getStartTime().isSetExactlyAt()) {
					try {
						later = w.getStartTime().getExactlyAt();
						// System.out.println("Later: " + later);
					} catch (Exception e) {
						System.err.println("Invalid time.");
						nErrors++;
					}
				}

			}

			nErrors += evaluteEarlyLateRelationship(cwf,
					util.createCausalRelationshipIDs(w.getCause().getRef(), w
							.getEffect().getRef()), earlier, later);

			if (w.isSetEndTime()) {
				if (w.getEndTime().isSetNoEarlierThan()) {
					try {
						later = w.getEndTime().getNoEarlierThan();
						// System.out.println("Earlier: " + earlier);
					} catch (Exception e) {
						System.err.println("Invalid time.");
						nErrors++;
					}
				}
				if (w.getEndTime().isSetNoLaterThan()) {
					try {
						if (later.after(w.getEndTime().getNoEarlierThan())) {
							later = w.getEndTime().getNoEarlierThan();
							nErrors++;
						}
						// System.out.println("Later: " + later);
					} catch (Exception e) {
						System.err.println("Invalid time.");
						nErrors++;
					}
				}

				if (w.getEndTime().isSetExactlyAt()) {
					try {
						later = w.getEndTime().getExactlyAt();
						// System.out.println("Later: " + later);
					} catch (Exception e) {
						System.err.println("Invalid time.");
						nErrors++;
					}
				}
			}

			nErrors += evaluteEarlyLateRelationship(cwf,
					util.createCausalRelationshipIDs(w.getCause().getRef(), w
							.getEffect().getRef()), earlier, later);

		} else {
			System.err.println("Unrecognized relationship:"
					+ relationshipClassName);
		}

		return nErrors;
	}

	public void getAnnoAnalysis(String cwf) {

		// Density analysis of annotations for OPM Vertices/Edges
		DecimalFormat df = new DecimalFormat("#.###");

		for (Object o : annoStats.keySet().toArray()) {

			// System.out.println(o + " - " + annoStats.get(o));
		}

		for (Object t : annoDensityByType.keySet().toArray()) {
			HashMap<Integer, Integer> densityByNAnnos = annoDensityByType
					.get(t);
			HashMap<Integer, Integer> densityByNAnnosNoDup = annoDensityByTypeNoDup
					.get(t);

			HashMap<Integer, Double> percentages = new HashMap<Integer, Double>();
			HashMap<Integer, Double> percentagesNoDup = new HashMap<Integer, Double>();
			int totalInGroup = 0;
			double maxPercentage = 0;
			int totalInGroupNoDup = 0;
			double maxPercentageNoDup = 0;

			System.out.println("\n=========With Duplicates Analysis==========");

			for (Object n : densityByNAnnos.values().toArray()) {
				totalInGroup += (Integer) n;
			}

			for (Object n : densityByNAnnos.keySet().toArray()) {
				double groupCount = densityByNAnnos.get(n);
				double percentage = ((groupCount / totalInGroup) * 100);
				percentages.put((Integer) n, percentage);
				if (percentage > maxPercentage)
					maxPercentage = percentage;

			}

			for (Object n : densityByNAnnos.keySet().toArray()) {
				double percentage = percentages.get(n);
				double ratio = (percentage / maxPercentage);
				System.out.println("Type: " + t + "\tAnnotations: " + n
						+ "\tOccurence: " + densityByNAnnos.get(n) + "\t"
						+ df.format(percentage) + "%");

				try {
					FileWriter duplicates;
					duplicates = new FileWriter(("config/output/dup"), true);
					if (ratio < 0.05)
						duplicates.write(cwf + "\tType: " + t
								+ "\tAnnotations: " + n + "\tOccurence: "
								+ densityByNAnnos.get(n)
								+ "\t--- Outlier group detected." + ratio
								+ "\n");
					else {
						duplicates.write(cwf + "\tNo outliers" + "\n");
					}
					duplicates.flush();

					duplicates.close();
				} catch (IOException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
				if (ratio < 0.05) {
					System.out.println("\t--- Outlier group detected." + ratio);

				}

			}

			System.out.println("\n=========No Duplicates Analysis==========");
			for (Object n : densityByNAnnosNoDup.values().toArray()) {
				totalInGroupNoDup += (Integer) n;
			}

			for (Object n : densityByNAnnosNoDup.keySet().toArray()) {
				double groupCount = densityByNAnnosNoDup.get(n);
				double percentage = ((groupCount / totalInGroup) * 100);
				percentages.put((Integer) n, percentage);
				if (percentage > maxPercentageNoDup)
					maxPercentageNoDup = percentage;

			}

			for (Object n : densityByNAnnosNoDup.keySet().toArray()) {
				double percentage = percentages.get(n);
				double ratio = (percentage / maxPercentageNoDup);
				System.out.println("Type: " + t + "\tAnnotations: " + n
						+ "\tOccurence: " + densityByNAnnosNoDup.get(n) + "\t"
						+ df.format(percentage) + "%");
				if (ratio < 0.05)
					System.out.println("\t--- Outlier group detected." + ratio);
			}

		}
	}

	public int getTemporalAnalysis(String cwf) {

		int nErrors = 0;
		try {
			FileWriter output = new FileWriter((TEMPORAL_ANNA_FILE
					+ cwf.replace(":", "+").replace("/", "_") + ".txt"), true);

			Object[] max = new Object[2];
			Object[] min = new Object[2];

			for (Object k : temporalCache.keySet().toArray()) {
				Calendar[] temporalRange = temporalCache.get(k);
				Calendar begin = temporalRange[0];
				Calendar end = temporalRange[1];
				long diff = 0;

				if (begin != null && end != null) {
					diff = (end.getTimeInMillis() - begin.getTimeInMillis()) / 1000;

					if (max[0] == null) {
						max[0] = diff;
						Vector<String> vector = new Vector<String>();
						vector.add(k.toString());
						max[1] = vector;

					} else {
						if (diff > Long.parseLong(max[0].toString())) {
							max[0] = diff;
							Vector<String> vector = new Vector<String>();
							vector.add(k.toString());
							max[1] = vector;
						} else if (diff == Long.parseLong(max[0].toString())) {
							Vector<String> vector = (Vector<String>) max[1];
							vector.add(k.toString());
							max[1] = vector;
						}
					}

					if (min[0] == null) {
						min[0] = diff;
						Vector<String> vector = new Vector<String>();
						vector.add(k.toString());
						min[1] = vector;

					} else {
						if (diff < Long.parseLong(min[0].toString())) {
							min[0] = diff;
							Vector<String> vector = new Vector<String>();
							vector.add(k.toString());
							min[1] = vector;
						} else if (diff == Long.parseLong(min[0].toString())) {
							Vector<String> vector = (Vector<String>) min[1];
							vector.add(k.toString());
							min[1] = vector;
						}
					}

					System.out.println(k + " " + diff);
				} else {
					System.out.println(k + " " + begin + " " + end);
				}
			}

			// Check consistency

			Vector<String> causes = new Vector<String>();
			Vector<String> effects = new Vector<String>();
			Vector<String> input = new Vector<String>();
			Vector<LinkedList<String>> lineage = new Vector<LinkedList<String>>();

			for (Object o : temporalCache.keySet().toArray()) {

				String[] split = o.toString().split("<-");
				String cause = split[0];
				String effect = split[1];
				causes.add(cause);
				effects.add(effect);
			}

			for (String c : causes) {
				if (!effects.contains(c)) {
					input.add(c);
				}
			}

			while (!input.isEmpty()) {
				String n = input.firstElement();
				input.remove(n);

				for (int i = 0; i < causes.size(); i++) {
					if (causes.get(i).equals(n)) {
						String cause = causes.get(i);
						String effect = effects.get(i);
						for (int j = 0; j < causes.size(); j++) {
							if (causes.get(j).equals(effect)) {
								LinkedList<String> l = new LinkedList<String>();
								l.add(cause);
								l.add(effect);
								l.add(effects.get(j));
								lineage.add(l);
							}
						}
						causes.remove(i);
						effects.remove(i);
						input.add(effect);
					}
				}
			}

			for (LinkedList<String> l : lineage) {
				Calendar[] temporalRange1 = temporalCache.get(l.toArray()[0]
						+ "<-" + l.toArray()[1]);
				Calendar[] temporalRange2 = temporalCache.get(l.toArray()[1]
						+ "<-" + l.toArray()[2]);
				// System.out.println(temporalRange1[0] + " " +
				// temporalRange1[1]
				// + " " + temporalRange2[0] + " " + temporalRange2[1]);
				if (temporalRange1[0] != null && temporalRange1[1] != null
						&& temporalRange2[0] != null
						&& temporalRange2[1] != null) {

					if (temporalRange1[0].before(temporalRange2[0])
							|| temporalRange1[0].equals(temporalRange2[0])) {
						// System.out
						// .println("First range start time is smaller or equals to 2nd range start time");
					} else {
						System.out.println(l.toArray()[0] + "<-"
								+ l.toArray()[1] + "<-" + l.toArray()[2]);
						System.out.println(temporalRange1[0] + " "
								+ temporalRange1[1]);
						System.out.println(temporalRange2[0] + " "
								+ temporalRange2[1]);
						System.out.println("---------------Hmm..");

						output.write(l.toArray()[0] + "<-" + l.toArray()[1]
								+ "<-" + l.toArray()[2] + "\n");
						output.write(temporalRange1[0] + " "
								+ temporalRange1[1] + "\n");
						output.write(temporalRange2[0] + " "
								+ temporalRange2[1] + "\n");

						nErrors++;
					}

					if (temporalRange1[1].before(temporalRange2[1])
							|| temporalRange1[1].equals(temporalRange2[1])) {
						// System.out
						// .println("First range end time is smaller or equals to 2nd range start time");
					} else {
						System.out.println(l.toArray()[0] + "<-"
								+ l.toArray()[1] + "<-" + l.toArray()[2]);
						System.out.println(temporalRange1[0] + " "
								+ temporalRange1[1]);
						System.out.println(temporalRange2[0] + " "
								+ temporalRange2[1]);
						System.out.println("---------------Hmm..");

						output.write(l.toArray()[0] + "<-" + l.toArray()[1]
								+ "<-" + l.toArray()[2] + "\n");
						output.write(temporalRange1[0] + " "
								+ temporalRange1[1] + "\n");
						output.write(temporalRange2[0] + " "
								+ temporalRange2[1] + "\n");

						nErrors++;
					}
				}
			}

			// System.out.println("Longest range: " + max[0]);
			// for (Object o : ((Vector<String>) max[1]).toArray()) {
			// System.out.println("\t" + o);
			// }
			//
			// System.out.println("Smallest range: " + min[0]);
			// for (Object o : ((Vector<String>) min[1]).toArray()) {
			// System.out.println("\t" + o);
			// }
			output.close();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}

		return nErrors;
	}
}
