/*******************************************************************************
 * Copyright (c) 2015 Eclipse RDF4J contributors, Aduna, and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Distribution License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/org/documents/edl-v10.php.
 *******************************************************************************/
package org.eclipse.rdf4j.rio.turtle;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.Reader;
import java.io.UnsupportedEncodingException;
import java.nio.charset.StandardCharsets;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;

import org.apache.commons.io.input.BOMInputStream;
import org.eclipse.rdf4j.common.text.ASCIIUtil;
import org.eclipse.rdf4j.model.IRI;
import org.eclipse.rdf4j.model.Literal;
import org.eclipse.rdf4j.model.Resource;
import org.eclipse.rdf4j.model.Statement;
import org.eclipse.rdf4j.model.Triple;
import org.eclipse.rdf4j.model.Value;
import org.eclipse.rdf4j.model.ValueFactory;
import org.eclipse.rdf4j.model.impl.SimpleValueFactory;
import org.eclipse.rdf4j.model.vocabulary.RDF;
import org.eclipse.rdf4j.model.vocabulary.XSD;
import org.eclipse.rdf4j.rio.RDFFormat;
import org.eclipse.rdf4j.rio.RDFHandlerException;
import org.eclipse.rdf4j.rio.RDFParseException;
import org.eclipse.rdf4j.rio.RioSetting;
import org.eclipse.rdf4j.rio.helpers.AbstractRDFParser;
import org.eclipse.rdf4j.rio.helpers.BasicParserSettings;
import org.eclipse.rdf4j.rio.helpers.TurtleParserSettings;

/**
 * RDF parser for <a href="https://www.w3.org/TR/turtle/">RDF-1.1 Turtle</a> files. This parser is not thread-safe,
 * therefore its public methods are synchronized.
 * <p>
 * <li>Normalization of integer, floating point and boolean values is dependent on the specified datatype handling.
 * According to the specification, integers and booleans should be normalized, but floats don't.</li>
 * <li>Comments can be used anywhere in the document, and extend to the end of the line. The Turtle grammar doesn't
 * allow comments to be used inside triple constructs that extend over multiple lines, but the author's own parser
 * deviates from this too.</li>
 * </ul>
 *
 * @author Arjohn Kampman
 * @author Peter Ansell
 */
public class TurtleParser extends AbstractRDFParser {

	/*-----------*
	 * Variables *
	 *-----------*/

	private BufferedReader reader;

	protected Resource subject;

	protected IRI predicate;

	protected Value object;

	private int lineNumber = 1;

	private final StringBuilder parsingBuilder = new StringBuilder();

	private static final String INSENSITIVE_PREFIX = "prefix";

	private static final String INSENSITIVE_BASE = "base";

	private static final String SENSITIVE_PREFIX = "@prefix";

	private static final String SENSITIVE_BASE = "@base";

	private String currentLine;

	private int currentIndex;

	/*--------------*
	 * Constructors *
	 *--------------*/

	/**
	 * Creates a new TurtleParser that will use a {@link SimpleValueFactory} to create RDF model objects.
	 */
	public TurtleParser() {
		super();
	}

	/**
	 * Creates a new TurtleParser that will use the supplied ValueFactory to create RDF model objects.
	 *
	 * @param valueFactory A ValueFactory.
	 */
	public TurtleParser(ValueFactory valueFactory) {
		super(valueFactory);
	}

	/*---------*
	 * Methods *
	 *---------*/

	@Override
	public RDFFormat getRDFFormat() {
		return RDFFormat.TURTLE;
	}

	@Override
	public Collection<RioSetting<?>> getSupportedSettings() {
		Set<RioSetting<?>> result = new HashSet<>(super.getSupportedSettings());
		result.add(TurtleParserSettings.CASE_INSENSITIVE_DIRECTIVES);
		result.add(TurtleParserSettings.ACCEPT_TURTLESTAR);
		return result;
	}

	@Override
	public synchronized void parse(InputStream in, String baseURI)
			throws IOException, RDFParseException, RDFHandlerException {
		if (in == null) {
			throw new IllegalArgumentException("Input stream must not be 'null'");
		}

		try {
			parse(new BufferedReader(new InputStreamReader(new BOMInputStream(in, false), StandardCharsets.UTF_8)),
					baseURI);
		} catch (UnsupportedEncodingException e) {
			// Every platform should support the UTF-8 encoding...
			throw new RuntimeException(e);
		}
	}

	@Override
	public synchronized void parse(Reader reader, String baseURI)
			throws IOException, RDFParseException, RDFHandlerException {
		clear();
		try {
			if (reader == null) {
				throw new IllegalArgumentException("Reader must not be 'null'");
			}
			if (rdfHandler != null) {
				rdfHandler.startRDF();
			}
			// Start counting lines at 1:
			lineNumber = 0;
			currentIndex = -1;

			if (!(reader instanceof BufferedReader)) {
				this.reader = new BufferedReader(reader);
			} else {
				this.reader = (BufferedReader) reader;
			}

			if (baseURI != null) {
				// Store normalized base URI
				setBaseURI(baseURI);
			}
			reportLocation();
			if (readLine()) {
				int startIndex = skipMultilineWSC(false);
				while (startIndex > -1) {
					parseStatement();
					startIndex = skipMultilineWSC(false);
				}
			}
		} finally {
			clear();
		}

		if (rdfHandler != null) {
			rdfHandler.endRDF();
		}
	}

	protected int parseStatement() throws IOException, RDFParseException, RDFHandlerException {
		if (!tryProcessDirective()) {
			parseTriples();
			skipMultilineWSC(true);
			return verifyStatementEndsWithDot();
		}
		return currentIndex;
	}

	private boolean tryProcessDirective() throws IOException {
		if (currentLine.charAt(currentIndex) == '@') {
			parseCaseSensitiveDirective();
			return true;
		}
		for (int i = 0; i < INSENSITIVE_PREFIX.length(); i++) {
			if (Character.toLowerCase(currentLine.charAt(currentIndex + i)) != INSENSITIVE_PREFIX.charAt(i)) {
				break;
			}
			if (i == INSENSITIVE_PREFIX.length() - 1) {
				currentIndex += INSENSITIVE_PREFIX.length();
				parsePrefixID(false);
				return true;
			}
		}
		for (int i = 0; i < INSENSITIVE_BASE.length(); i++) {
			if (Character.toLowerCase(currentLine.charAt(currentIndex + i)) != INSENSITIVE_BASE.charAt(i)) {
				break;
			}
			if (i == INSENSITIVE_BASE.length() - 1) {
				currentIndex += INSENSITIVE_BASE.length();
				parseBase(false);
				return true;
			}
		}
		return false;
	}

	private void parseCaseSensitiveDirective() throws IOException {
		String directive = currentLine.substring(currentIndex);
		if (directive.startsWith(SENSITIVE_PREFIX)) {
			currentIndex += SENSITIVE_PREFIX.length();
			parsePrefixID(true);
		} else if (directive.startsWith(SENSITIVE_BASE)) {
			currentIndex += SENSITIVE_BASE.length();
			parseBase(true);
		} else if (directive.substring(0, 7).equalsIgnoreCase(SENSITIVE_PREFIX)) {
			if (!this.getParserConfig().get(TurtleParserSettings.CASE_INSENSITIVE_DIRECTIVES)) {
				reportFatalError("Cannot strictly support case-insensitive @prefix directive in compliance mode.");
			}
			currentIndex += SENSITIVE_PREFIX.length();
			parsePrefixID(true);
		} else if (directive.substring(0, 5).equalsIgnoreCase(SENSITIVE_BASE)) {
			if (!this.getParserConfig().get(TurtleParserSettings.CASE_INSENSITIVE_DIRECTIVES)) {
				reportFatalError("Cannot strictly support case-insensitive @base directive in compliance mode.");
			}
			currentIndex += SENSITIVE_BASE.length();
			parseBase(true);
		} else {
			reportFatalError("Unknown directive \"" + directive + "\"");
		}
	}

	protected void parsePrefixID(boolean isSensitive) throws IOException, RDFParseException, RDFHandlerException {
		// Read prefix ID (e.g. "rdf:" or ":")
		int tempIndex = skipInlineWSC();
		int tempEndIndex = readUpToCharOrWSC(':');
		if (TurtleUtil.isWhitespace(currentLine.charAt(currentIndex))) {
			skipInlineWSC();
		}
		if (currentLine.charAt(currentIndex) == ':') {
			currentIndex++;
		}
		String prefixStr = currentLine.substring(tempIndex, tempEndIndex);
		skipInlineWSC();
		// Read the namespace URI
		IRI namespace = parseURI();
		String namespaceStr = namespace.toString();

		// Store and report this namespace mapping
		setNamespace(prefixStr, namespaceStr);

		if (rdfHandler != null) {
			rdfHandler.handleNamespace(prefixStr, namespaceStr);
		}
		if (isSensitive) {
			verifyStatementEndsWithDot();
		}
	}

	protected void parseBase(boolean isSensitive) throws IOException, RDFParseException,
			RDFHandlerException {
		IRI baseURI = parseURI();

		setBaseURI(baseURI.toString());
		if (isSensitive) {
			verifyStatementEndsWithDot();
		}
	}

	protected void parseTriples() throws IOException, RDFParseException, RDFHandlerException {
		// If the first character is an open bracket we need to decide which of
		// the two parsing methods for blank nodes to use
		if (currentLine.charAt(currentIndex) == '[') {
			// skipToNextIndex();
			if (currentLine.charAt(currentIndex) == ']') {
				readCodePoint();
				subject = createNode();
				skipMultilineWSC(true);
				parsePredicateObjectList();
			} else {
				subject = parseImplicitBlank();
			}
			skipMultilineWSC(true);
			// if this is not the end of the statement, recurse into the list of
			// predicate and objects, using the subject parsed above as the
			// subject
			// of the statement.
			if (currentLine.charAt(currentIndex) != '.') {
				parsePredicateObjectList();
			}
		} else {
			parseSubject();
			skipMultilineWSC(true);
			parsePredicateObjectList();
		}

		subject = null;
		predicate = null;
		object = null;
	}

	protected void parsePredicateObjectList() throws IOException, RDFParseException, RDFHandlerException {
		parsePredicate();
		skipMultilineWSC(true);

		parseObjectList();

		skipMultilineWSC(true);
		while (currentLine.charAt(currentIndex) == ';') {
			skipToNextIndex();
			skipMultilineWSC(true);
			int c = currentLine.charAt(currentIndex);

			if (c == '.' || // end of triple
					c == ']' || c == '}') // end of predicateObjectList inside
			{
				break;
			} else if (c == ';') {
				// empty predicateObjectList, skip to next
				skipToNextIndex();
				skipMultilineWSC(true);
				continue;
			}
			parsePredicate();

			skipMultilineWSC(true);

			parseObjectList();
		}
	}

	protected void parseObjectList() throws IOException, RDFParseException, RDFHandlerException {
		parseObject();
		skipMultilineWSC(true);
		while (currentLine.charAt(currentIndex) == ',') {
			currentIndex++;
			skipMultilineWSC(true);
			parseObject();
		}
	}

	protected void parseSubject() throws IOException, RDFParseException, RDFHandlerException {
		char c = currentLine.charAt(currentIndex);
		if (c == '(') {
			subject = parseCollection();
		} else if (c == '[') {
			subject = parseImplicitBlank();
		} else {
			Value value = parseValue();

			if (value instanceof Resource) {
				subject = (Resource) value;
			} else {
				if (value != null) {
					reportFatalError("Illegal subject value: " + value);
				}
			}
		}
	}

	protected void parsePredicate() throws IOException, RDFParseException, RDFHandlerException {
		// Check if the short-cut 'a' is used
		char c = currentLine.charAt(currentIndex);
		if (c == 'a') {
			if (currentLine.length() == (currentIndex + 1) || TurtleUtil.isWhitespace(
					currentLine.charAt(currentIndex + 1))) {
				skipToNextIndex();
				// Short-cut is used, return the rdf:type URI
				predicate = RDF.TYPE;
			}
		} else if (c == '<') {
			// uriref, e.g. <foo://bar>
			predicate = parseURI();
		} else if (c == ':' || TurtleUtil.isPrefixStartChar(c)) {
			// qname or boolean
			Value value = parseQNameOrBoolean();
			if (!(value instanceof IRI)) {
				reportFatalError("Expected an IRI here, found '" + new String(Character.toChars(c)) + "' of type "
						+ value.getClass().getSimpleName());
			}
			predicate = (IRI) value;
		} else {
			reportFatalError("Expected an RDF Predicate here, found '" + new String(Character.toChars(c)) + "'");
		}
	}

	protected void parseObject() throws IOException, RDFParseException, RDFHandlerException {
		switch (currentLine.charAt(currentIndex)) {
		case '(':
			object = parseCollection();
			break;
		case '[':
			object = parseImplicitBlank();
			break;
		default:
			object = parseValue();
			reportStatement(subject, predicate, object);
			break;
		}
	}

	/**
	 * Parses a collection, e.g. <tt>( item1 item2 item3 )</tt>.
	 */
	protected Resource parseCollection() throws IOException, RDFParseException, RDFHandlerException {
		verifyCharacterOrFail(currentLine.charAt(currentIndex), "(");
		skipToNextIndex();
		skipMultilineWSC(true);
		int c = currentLine.charAt(currentIndex);
		if (c == ')') {
			// Empty list
			skipToNextIndex();
			if (subject != null) {
				reportStatement(subject, predicate, RDF.NIL);
			}
			return RDF.NIL;
		} else {
			Resource listRoot = createNode();
			if (subject != null) {
				reportStatement(subject, predicate, listRoot);
			}
			// Remember current subject and predicate
			Resource oldSubject = subject;
			IRI oldPredicate = predicate;

			// generated bNode becomes subject, predicate becomes rdf:first
			subject = listRoot;
			predicate = RDF.FIRST;

			parseObject();

			skipMultilineWSC(true);

			Resource bNode = listRoot;

			while (currentLine.charAt(currentIndex) != ')') {
				// Create another list node and link it to the previous
				Resource newNode = createNode();
				reportStatement(bNode, RDF.REST, newNode);

				// New node becomes the current
				subject = bNode = newNode;

				parseObject();
				skipMultilineWSC(true);
			}
			skipToNextIndex();
			skipMultilineWSC(true);
			// Close the list
			reportStatement(bNode, RDF.REST, RDF.NIL);

			// Restore previous subject and predicate
			subject = oldSubject;
			predicate = oldPredicate;

			return listRoot;
		}
	}

	/**
	 * Parses an implicit blank node. This method parses the token <tt>[]</tt> and predicateObjectLists that are
	 * surrounded by square brackets.
	 */
	protected Resource parseImplicitBlank() throws IOException, RDFParseException, RDFHandlerException {
		readCodePoint();
		skipMultilineWSC(true);
		Resource bNode = createNode();
		if (subject != null) {
			reportStatement(subject, predicate, bNode);
		}
		// skipMultilineWSC(true);
		// readCodePoint();
		if (currentLine.charAt(currentIndex) != ']') {
			// Remember current subject and predicate
			Resource oldSubject = subject;
			IRI oldPredicate = predicate;

			// generated bNode becomes subject
			subject = bNode;

			// Enter recursion with nested predicate-object list
			skipMultilineWSC(true);

			parsePredicateObjectList();

			skipMultilineWSC(true);
			// Read closing bracket
			verifyCharacterOrFail(currentLine.charAt(currentIndex), "]");
			skipToNextIndex();
			// Restore previous subject and predicate
			subject = oldSubject;
			predicate = oldPredicate;
		} else {
			readCodePoint();
		}
		return bNode;
	}

	protected Value parseValue() throws IOException, RDFParseException, RDFHandlerException {
		if (getParserConfig().get(TurtleParserSettings.ACCEPT_TURTLESTAR) && peekIsTripleValue()) {
			return parseTripleValue();
		}
		char c = currentLine.charAt(currentIndex);
		if (c == '<') {
			// uriref, e.g. <foo://bar>
			return parseURI();
		} else if (c == ':' || TurtleUtil.isPrefixStartChar(c)) {
			// qname or boolean
			return parseQNameOrBoolean();
		} else if (c == '_') {
			// node ID, e.g. _:n1
			return parseNodeID();
		} else if (c == '"' || c == '\'') {
			// quoted literal, e.g. "foo" or """foo""" or 'foo' or '''foo'''
			return parseQuotedLiteral();
		} else if (ASCIIUtil.isNumber(c) || c == '.' || c == '+' || c == '-') {
			// integer or double, e.g. 123 or 1.2e3
			return parseNumber();
		} else {
			reportFatalError("Expected an RDF value here, found '" + new String(Character.toChars(c)) + "'");
			return null;
		}
	}

	/**
	 * Parses a quoted string, optionally followed by a language tag or datatype.
	 */
	protected Literal parseQuotedLiteral() throws IOException, RDFParseException, RDFHandlerException {
		String label = parseQuotedString();
		readCodePoint();
		skipMultilineWSC(true);
		// Check for presence of a language tag or datatype
		char c = currentLine.charAt(currentIndex);
		if (c == '@') {
			// Read language
			StringBuilder lang = getBuilder();

			c = readCodePoint();
			if (c == -1) {
				throwEOFException();
			}

			boolean verifyLanguageTag = getParserConfig().get(BasicParserSettings.VERIFY_LANGUAGE_TAGS);
			if (verifyLanguageTag && !TurtleUtil.isLanguageStartChar(c)) {
				reportError("Expected a letter, found '" + new String(Character.toChars(c)) + "'",
						BasicParserSettings.VERIFY_LANGUAGE_TAGS);
			}

			appendCodepoint(lang, c);

			c = readCodePoint();
			while (!TurtleUtil.isWhitespace(c)) {
				// SES-1887 : Flexibility introduced for SES-1985 and SES-1821
				// needs
				// to be counterbalanced against legitimate situations where
				// Turtle
				// language tags do not need whitespace following the language
				// tag
				if (c == '.' || c == ';' || c == ',' || c == ')' || c == ']' || c == '>' || c == -1) {
					break;
				}
				if (verifyLanguageTag && !TurtleUtil.isLanguageChar(c)) {
					reportError("Illegal language tag char: '" + new String(Character.toChars(c)) + "'",
							BasicParserSettings.VERIFY_LANGUAGE_TAGS);
				}
				appendCodepoint(lang, c);
				c = readCodePoint();
			}
			skipMultilineWSC(true);
			return createLiteral(label, lang.toString(), null, getLineNumber(), -1);
		} else if (c == '^') {

			// next character should be another '^'
			verifyCharacterOrFail(readCodePoint(), "^");
			skipToNextIndex();
			skipMultilineWSC(true);
			// Read datatype
			Value datatype = parseValue();
			if (datatype == null) {
				// the datatype IRI could not be parsed. report as error only if VERIFY_URI_SYNTAX is enabled, silently
				// skip otherwise.
				reportError("Invalid datatype IRI for literal '" + label + "'", BasicParserSettings.VERIFY_URI_SYNTAX);
				return null;
			} else if (!(datatype instanceof IRI)) {
				reportFatalError("Illegal datatype value: " + datatype);
			}
			return createLiteral(label, null, (IRI) datatype, getLineNumber(), -1);
		} else {
			// readCodePoint();
			// skipMultilineWSC(true);
			return createLiteral(label, null, null, getLineNumber(), -1);
		}
	}

	/**
	 * Parses a quoted string, which is either a "normal string" or a """long string""".
	 *
	 * @return string
	 * @throws IOException
	 * @throws RDFParseException
	 */
	protected String parseQuotedString() throws IOException, RDFParseException {
		String result = null;

		char c1 = currentLine.charAt(currentIndex);

		// First character should be '"' or "'"
		verifyCharacterOrFail(c1, "\"'");

		// Check for long-string, which starts and ends with three double quotes
		int c2 = currentLine.charAt(currentIndex + 1);
		int c3 = currentLine.charAt(currentIndex + 2);

		if ((c1 == '"' && c2 == '"' && c3 == '"') || (c1 == '\'' && c2 == '\'' && c3 == '\'')) {
			// Long string
			currentIndex += 2;
			result = parseLongString(c2);
		} else {
			// Normal string
			result = parseString(c1);
		}

		// Unescape any escape sequences
		try {
			result = TurtleUtil.decodeString(result);
		} catch (IllegalArgumentException e) {
			reportError(e.getMessage(), BasicParserSettings.VERIFY_DATATYPE_VALUES);
		}
		return result;
	}

	/**
	 * Parses a "normal string". This method requires that the opening character has already been parsed.
	 *
	 * @return parsed string
	 * @throws IOException
	 * @throws RDFParseException
	 */
	protected String parseString(int closingCharacter) throws IOException, RDFParseException {
		// StringBuilder sb = getBuilder();
		// while (true) {
		// int c;
		// try {
		// c = currentLine.charAt(++currentIndex);
		// } catch (IndexOutOfBoundsException e) {
		// reportFatalError("Illegal carriage return or new line in literal");
		// c = -1;
		// }
		//
		// if (c == closingCharacter) {
		// break;
		// } else if (c == -1) {
		// throwEOFException();
		// }
		//
		// appendCodepoint(sb, c);
		//
		// if (c == '\\') {
		// // This escapes the next character, which might be a '"'
		// c = readCodePoint();
		// if (c == (char) -1) {
		// throwEOFException();
		// }
		// appendCodepoint(sb, c);
		// }
		// }

		// return sb.toString();
		int temp = currentIndex + 1;
		if (list.isEmpty()) {
			throwEOFException();
		}
		currentIndex = list.removeFirst();
		return currentLine.substring(temp, currentIndex);
	}

	/**
	 * Parses a """long string""". This method requires that the first three characters have already been parsed.
	 */
	protected String parseLongString(int closingCharacter) throws IOException, RDFParseException {
		// StringBuilder sb = getBuilder();
		// int doubleQuoteCount = 0;
		// char c;
		// while (doubleQuoteCount < 3) {
		// c = readCodePoint();
		// if (c == (char) -1) {
		// throwEOFException();
		// }
		// if (c == closingCharacter) {
		// doubleQuoteCount++;
		// } else {
		// doubleQuoteCount = 0;
		// }
		// appendCodepoint(sb, c);
		// if (c == '\\') {
		// // This escapes the next character, which might be a '"'
		// c = readCodePoint();
		// if (c == (char) -1) {
		// throwEOFException();
		// }
		// appendCodepoint(sb, c);
		// }
		// }
		//
		// return sb.substring(0, sb.length() - 3);
		int temp = currentIndex + 1;
		currentIndex = list.removeFirst();
		return currentLine.substring(temp, currentIndex - 2);
	}

	protected Literal parseNumber() throws IOException, RDFParseException {
		StringBuilder value = getBuilder();
		IRI datatype = XSD.INTEGER;

		int c = currentLine.charAt(currentIndex);

		// read optional sign character
		if (c == '+' || c == '-') {
			appendCodepoint(value, c);
			c = readCodePoint();
		}

		while (ASCIIUtil.isNumber(c)) {
			appendCodepoint(value, c);
			c = readCodePoint();
		}

		if (c == '.' || c == 'e' || c == 'E') {

			// read optional fractional digits
			if (c == '.') {

				if ((currentLine.length() - 1 == currentIndex)
						|| TurtleUtil.isWhitespace(currentLine.charAt(currentIndex + 1))) {
					// We're parsing an integer that did not have a space before
					// the
					// period to end the statement
				} else {
					appendCodepoint(value, c);

					c = readCodePoint();

					while (ASCIIUtil.isNumber(c)) {
						appendCodepoint(value, c);
						c = readCodePoint();
					}

					if (value.length() == 1) {
						// We've only parsed a '.'
						reportFatalError("Object for statement missing");
					}

					// We're parsing a decimal or a double
					datatype = XSD.DECIMAL;
				}
			} else {
				if (value.length() == 0) {
					// We've only parsed an 'e' or 'E'
					reportFatalError("Object for statement missing");
				}
			}

			// read optional exponent
			if (c == 'e' || c == 'E') {
				datatype = XSD.DOUBLE;
				appendCodepoint(value, c);

				c = readCodePoint();
				if (c == '+' || c == '-') {
					appendCodepoint(value, c);
					c = readCodePoint();
				}

				if (!ASCIIUtil.isNumber(c)) {
					reportError("Exponent value missing", BasicParserSettings.VERIFY_DATATYPE_VALUES);
				}

				appendCodepoint(value, c);

				c = readCodePoint();
				while (ASCIIUtil.isNumber(c)) {
					appendCodepoint(value, c);
					c = readCodePoint();
				}
			}
		}

		// Unread last character, it isn't part of the number
		return createLiteral(value.toString(), null, datatype, getLineNumber(), -1);
	}

	protected IRI parseURI() throws RDFParseException, IOException {
		// First character should be '<'
		skipMultilineWSC(true);
		verifyCharacterOrFail(currentLine.charAt(currentIndex), "<");
		currentIndex++;
		if (currentIndex > currentLine.length()) {
			throwEOFException();
		}
		StringBuilder temp = getBuilder();
		boolean uriIsIllegal = false;
		for (int i = currentIndex; i < currentLine.length(); i++) {
			char c = currentLine.charAt(i);
			if (c == '>') {
				currentIndex = i;
				skipToNextIndex();
				skipInlineWSC();
				break;
			}
			if (c == ' ') {
				reportError("IRI included an unencoded space: '" + c + "'", BasicParserSettings.VERIFY_URI_SYNTAX);
				uriIsIllegal = true;
			}
			if (c == '\\') {
				// This escapes the next character, which might be a '>'
				c = readCodePoint();
				if (c == (char) -1) {
					throwEOFException();
				}
				if (c != 'u' && c != 'U') {
					reportError("IRI includes string escapes: '\\" + c + "'",
							BasicParserSettings.VERIFY_URI_SYNTAX);
					uriIsIllegal = true;
				}
				appendCodepoint(temp, c);
				continue;
			}
			// if (TurtleUtil.isWhitespace(currentLine.charAt(i))) {
			// // reportError("IRI included an unencoded space: '" + currentLine.charAt(i) + "'",
			// // BasicParserSettings.VERIFY_URI_SYNTAX);
			// uriIsIllegal = true;
			// appendCodepoint(temp, c);
			// continue;
			// }
			appendCodepoint(temp, c);
			// do not report back the actual URI if it's illegal and the parser is
			// configured to verify URI syntax.
		}
		if (!(uriIsIllegal && getParserConfig().get(BasicParserSettings.VERIFY_URI_SYNTAX))) {
			String uri = temp.toString();

			// Unescape any escape sequences
			try {
				// FIXME: The following decodes \n and similar in URIs, which
				// should
				// be
				// invalid according to test <turtle-syntax-bad-uri-04.ttl>
				uri = TurtleUtil.decodeString(uri);
			} catch (IllegalArgumentException e) {
				reportError(e.getMessage(), BasicParserSettings.VERIFY_DATATYPE_VALUES);
			}
			return super.resolveURI(uri);
		}
		// throwEOFException();
		return null;
	}

	/**
	 * Parses qnames and boolean values, which have equivalent starting characters.
	 */
	protected Value parseQNameOrBoolean() throws IOException, RDFParseException {
		// First character should be a ':' or a letter
		char c = currentLine.charAt(currentIndex);
		if (c != ':' && !TurtleUtil.isPrefixStartChar(c)) {
			reportError("Expected a ':' or a letter, found '" + new String(Character.toChars(c)) + "'",
					BasicParserSettings.VERIFY_RELATIVE_URIS);
		}
		String namespace = null;
		int startIndex = currentIndex;
		int prefixIndex = currentIndex;
		if (c == ':') {
			// qname using default namespace
			namespace = getNamespace("");
		} else {
			// c is the first letter of the prefix
			while (TurtleUtil.isPrefixChar(currentLine.charAt(prefixIndex))) {
				if (currentIndex == currentLine.length() - 1) {
					break;
				}
				prefixIndex++;
				currentIndex++;
			}
			// while (currentLine.charAt(prefixIndex) == '.' && prefixIndex > startIndex) {
			// prefixIndex--;
			// }
			skipMultilineWSC(true);
			c = currentLine.charAt(currentIndex);
			String value = currentLine.substring(startIndex, prefixIndex);
			if (c != ':') {
				// prefix may actually be a boolean value
				if (value.equals("true")) {
					return createLiteral("true", null, XSD.BOOLEAN, getLineNumber(), -1);
				} else if (value.equals("false")) {
					return createLiteral("false", null, XSD.BOOLEAN, getLineNumber(), -1);
				}
			}
			verifyCharacterOrFail(c, ":");

			namespace = getNamespace(value);
		}
		StringBuilder localName = getBuilder();
		// c == ':', read optional local name
		c = readCodePoint();
		if (TurtleUtil.isNameStartChar(c)) {
			if (c == '\\') {
				localName.append(readLocalEscapedChar());
			} else {
				appendCodepoint(localName, c);
			}
			c = readCodePoint();
			int prev = c;
			while (TurtleUtil.isNameChar(c)) {
				if (c == '.' && (currentLine.length() - 1 == currentIndex)) {
					// currentIndex--
					break;
				}
				if (c == '\\') {
					localName.append(readLocalEscapedChar());
				} else {
					appendCodepoint(localName, c);
				}
				prev = c;
				c = readCodePoint();
			}
			if (prev == '.') {
				localName.deleteCharAt(localName.length() - 1);
				currentIndex--;
			}
		}

		String localNameString = localName.toString();

		for (int i = 0; i < localNameString.length(); i++) {
			if (localNameString.charAt(i) == '%') {
				if (i > localNameString.length() - 3 || !ASCIIUtil.isHex(localNameString.charAt(i + 1))
						|| !ASCIIUtil.isHex(localNameString.charAt(i + 2))) {
					reportFatalError("Found incomplete percent-encoded sequence: " + localNameString);
				}
			}
		}

		// Note: namespace has already been resolved
		return createURI(namespace + localNameString);
	}

	private char readLocalEscapedChar() throws RDFParseException, IOException {
		int c = readCodePoint();

		if (TurtleUtil.isLocalEscapedChar(c)) {
			return (char) c;
		} else {
			throw new RDFParseException("found '" + new String(Character.toChars(c)) + "', expected one of: "
					+ Arrays.toString(TurtleUtil.LOCAL_ESCAPED_CHARS));
		}
	}

	private void skipToNextIndex() throws IOException {
		if (currentLine.length() - 1 > currentIndex) {
			currentIndex++;
		} else {
			currentIndex = 0;
			if (!readLine()) {
				throwEOFException();
			}
			skipMultilineWSC(true);
		}
	}

	/**
	 * Parses a blank node ID, e.g. <tt>_:node1</tt>.
	 */
	protected Resource parseNodeID() throws IOException, RDFParseException {
		// Node ID should start with "_:"
		verifyCharacterOrFail(currentLine.charAt(currentIndex), "_");
		verifyCharacterOrFail(readCodePoint(), ":");

		char c = currentLine.charAt(++currentIndex);
		if (!TurtleUtil.isBLANK_NODE_LABEL_StartChar(currentLine.charAt(currentIndex))) {
			reportError("Expected a letter, found '" + c + "'", BasicParserSettings.PRESERVE_BNODE_IDS);
		}

		StringBuilder name = getBuilder();
		appendCodepoint(name, c);

		// Read all following letter and numbers, they are part of the name
		c = readCodePoint();

		while (TurtleUtil.isBLANK_NODE_LABEL_Char(c)) {
			if (currentIndex == (currentLine.length() - 1)) {
				skipToNextIndex();
				break;
			}
			// todo update
			char previous = c;
			c = currentLine.charAt(++currentIndex);

			if (previous == '.' && (TurtleUtil.isWhitespace(c) || c == '<' || c == '_')) {
				currentIndex--;
				break;
			}
			appendCodepoint(name, previous);
		}
		skipMultilineWSC(true);
		return createNode(name.toString());
	}

	protected void reportStatement(Resource subj, IRI pred, Value obj) throws RDFParseException, RDFHandlerException {
		if (subj != null && pred != null && obj != null) {
			Statement st = createStatement(subj, pred, obj);
			if (rdfHandler != null) {
				rdfHandler.handleStatement(st);
			}
		}
	}

	/**
	 * Verifies that the supplied character code point <tt>codePoint</tt> is one of the expected characters specified in
	 * <tt>expected</tt>. This method will throw a <tt>ParseException</tt> if this is not the case.
	 */
	protected void verifyCharacterOrFail(int codePoint, String expected) throws RDFParseException {
		if (codePoint == -1) {
			throwEOFException();
		}

		final String supplied = new String(Character.toChars(codePoint));

		if (!expected.contains(supplied)) {
			StringBuilder msg = new StringBuilder(32);
			msg.append("Expected ");
			for (int i = 0; i < expected.length(); i++) {
				if (i > 0) {
					msg.append(" or ");
				}
				msg.append('\'');
				msg.append(expected.charAt(i));
				msg.append('\'');
			}
			msg.append(", found '");
			msg.append(supplied);
			msg.append("'");

			reportFatalError(msg.toString());
		}
	}

	protected int skipInlineWSC() throws RDFHandlerException {
		if (currentIndex > currentLine.length()) {
			throwEOFException();
		}
		for (int i = currentIndex; i < currentLine.length(); i++) {
			if (TurtleUtil.isWhitespace(currentLine.charAt(i))) {
				continue;
			}
			currentIndex = i;
			return i;
		}
		return -1;
	}

	protected int skipMultilineWSC(boolean shouldThrowEOF) throws RDFHandlerException, IOException {
		boolean moveToNextLine = false;
		do {
			if (moveToNextLine && !readLine()) {
				if (shouldThrowEOF) {
					throwEOFException();
				} else {
					return -1;
				}
			}
			if (!moveToNextLine && currentIndex > -1) {
				if (currentLine == null) {
					return -1;
				}
				for (int i = currentIndex; i < currentLine.length(); i++) {
					if (TurtleUtil.isWhitespace(currentLine.charAt(i))) {
						continue;
					} else if (currentLine.charAt(i) == '#') {
						currentIndex = i;
						processComment();
						break;
					}
					currentIndex = i;
					return i;
				}
			} else {
				for (int i = 0; i < currentLine.length(); i++) {
					if (TurtleUtil.isWhitespace(currentLine.charAt(i))) {
						continue;
					} else if (currentLine.charAt(i) == '#') {
						currentIndex = i;
						processComment();
						break;
					}
					currentIndex = i;
					return i;
				}
			}
			moveToNextLine = true;
		} while (moveToNextLine);
		currentIndex = -1;
		return -1;
	}

	protected int readUpToCharOrWSC(char targetChar) throws RDFHandlerException {
		if (currentIndex > currentLine.length()) {
			throwEOFException();
		}
		for (int i = currentIndex; i < currentLine.length(); i++) {
			if (TurtleUtil.isWhitespace(currentLine.charAt(i)) || currentLine.charAt(i) == targetChar) {
				currentIndex = i;
				return i;
			}
		}
		throwEOFException();
		return -1;
	}

	protected int verifyStatementEndsWithDot() throws RDFHandlerException, IOException {
		boolean moveToNextLine = false;
		do {
			if (moveToNextLine && !readLine()) {
				return -1;
			}
			for (int i = currentIndex; i < currentLine.length(); i++) {
				if (TurtleUtil.isWhitespace(currentLine.charAt(i))) {
					continue;
				} else if (currentLine.charAt(i) == '.') {
					if (currentLine.length() - 1 > currentIndex) {
						currentIndex++;
						return currentIndex;
					} else {
						currentIndex = 0;
						if (!readLine()) {
							return -1;
						}
						return skipMultilineWSC(false);
					}
				} else {
					reportFatalError("Line should have ended with dot");
				}
			}
			moveToNextLine = true;
		} while (moveToNextLine);
		return -1;
	}

	/**
	 * Reads the next Unicode code point.
	 *
	 * @return the next Unicode code point, or -1 if the end of the stream has been reached.
	 */
	protected char readCodePoint() throws IOException {
		try {
			return currentLine.charAt(++currentIndex);
		} catch (IndexOutOfBoundsException e) {
			while (readLine()) {
				if (currentLine.length() > 0) {
					currentIndex = 0;
					break;
				}
			}
			if (currentLine == null) {
				throwEOFException();
			}
			return currentLine.charAt(currentIndex);
		}
	}

	protected boolean processComment() throws RDFHandlerException {
		if (rdfHandler != null) {
			rdfHandler.handleComment(currentLine.substring(currentIndex));
		}
		return true;
	}

	private StringBuilder builder = new StringBuilder(100);

	private final static String EMPTY = "";

	private final AtomicInteger count = new AtomicInteger(0);

	private final LinkedList<Integer> list = new LinkedList<>();

	protected boolean readLine() throws IOException {
		list.clear();
		count.set(0);
		builder.setLength(0);
		int i;
		int enclosing = -1;
		int enclosingCount = 0;
		int prevChar = -1;
		int prevCount = 0;
		while ((i = readCode()) != -1) {
			if (i == '\'' || i == '\"') {
				if (enclosingCount == 0) {
					appendCodepoint(builder, i, count);
					enclosing = i;
					prevChar = i;
					i = readOrThrow();
					if (i == enclosing) {
						appendCodepoint(builder, i, count);
						i = readOrThrow();
						if (i == enclosing) {
							enclosingCount = 3;
						}
					} else {
						enclosingCount = 1;
					}
				} else {
					if (i == enclosing && (prevChar != '\\' || prevCount % 2 == 0)) {
						if (enclosingCount == 1) {
							list.add(count.intValue());
							enclosingCount = 0;
						} else {
							// count is 3
							prevChar = i;
							appendCodepoint(builder, i, count);
							i = readOrThrow();
							if (i == enclosing) {
								appendCodepoint(builder, i, count);
								i = readOrThrow();
								if (i == enclosing) {
									enclosingCount = 0;
									list.add(count.intValue());
								}
							}
						}
					}
				}
			}
			if (i == '\n' || i == '\r') {
				if (enclosingCount > 1) {
					count.incrementAndGet();
					builder.append((char) i);
					continue;
				} else {
					if (builder.length() > 0) {
						currentLine = builder.toString();
					} else {
						currentLine = EMPTY;
					}
					lineNumber++;
					reportLocation();
					return true;
				}
			}
			prevChar = i;
			if (i == '\\') {
				prevCount++;
			} else {
				prevCount = 0;
			}
			appendCodepoint(builder, i, count);
		}
		if (builder.length() > 0) {
			currentLine = builder.toString();
			lineNumber++;
			reportLocation();
			return true;
		}
		currentLine = null;
		return false;
	}

	private int readOrThrow() throws IOException {
		int next = reader.read();
		if (next == -1) {
			throwEOFException();
		}
		if (Character.isHighSurrogate((char) next)) {
			next = Character.toCodePoint((char) next, (char) reader.read());
		}
		return next;
	}

	private int readCode() throws IOException {
		int next = reader.read();
		if (Character.isHighSurrogate((char) next)) {
			next = Character.toCodePoint((char) next, (char) reader.read());
		}
		return next;
	}

	protected void reportLocation() {
		reportLocation(getLineNumber(), -1);
	}

	/**
	 * Overrides {@link AbstractRDFParser#reportWarning(String)}, adding line number information to the error.
	 */
	@Override
	protected void reportWarning(String msg) {
		reportWarning(msg, getLineNumber(), -1);
	}

	/**
	 * Overrides {@link AbstractRDFParser#reportError(String, RioSetting)}, adding line number information to the error.
	 */
	@Override
	protected void reportError(String msg, RioSetting<Boolean> setting) throws RDFParseException {
		reportError(msg, getLineNumber(), -1, setting);
	}

	/**
	 * Overrides {@link AbstractRDFParser#reportFatalError(String)}, adding line number information to the error.
	 */
	@Override
	protected void reportFatalError(String msg) throws RDFParseException {
		reportFatalError(msg, getLineNumber(), -1);
	}

	/**
	 * Overrides {@link AbstractRDFParser#reportFatalError(Exception)}, adding line number information to the error.
	 */
	@Override
	protected void reportFatalError(Exception e) throws RDFParseException {
		reportFatalError(e, getLineNumber(), -1);
	}

	protected void throwEOFException() throws RDFParseException {
		throw new RDFParseException("Unexpected end of file");
	}

	protected int getLineNumber() {
		return lineNumber;
	}

	private StringBuilder getBuilder() {
		parsingBuilder.setLength(0);
		return parsingBuilder;
	}

	/**
	 * Appends the characters from codepoint into the string builder. This is the same as Character#toChars but prevents
	 * the additional char array garbage for BMP codepoints.
	 *
	 * @param dst       the destination in which to append the characters
	 * @param codePoint the codepoint to be appended
	 */
	private static void appendCodepoint(StringBuilder dst, int codePoint) {
		if (Character.isBmpCodePoint(codePoint)) {
			dst.append((char) codePoint);
		} else if (Character.isValidCodePoint(codePoint)) {
			dst.append(Character.highSurrogate(codePoint));
			dst.append(Character.lowSurrogate(codePoint));
		} else {
			throw new IllegalArgumentException("Invalid codepoint " + codePoint);
		}
	}

	private static void appendCodepoint(StringBuilder dst, int codePoint, AtomicInteger count) {
		count.incrementAndGet();
		if (Character.isBmpCodePoint(codePoint)) {
			dst.append((char) codePoint);
		} else if (Character.isValidCodePoint(codePoint)) {
			count.incrementAndGet();
			dst.append(Character.highSurrogate(codePoint));
			dst.append(Character.lowSurrogate(codePoint));
		} else {
			throw new IllegalArgumentException("Invalid codepoint " + codePoint);
		}
	}

	/**
	 * Peeks at the next two Unicode code points without advancing the reader and returns true if they indicate the
	 * start of an RDF* triple value. Such values start with '<<'.
	 *
	 * @return true if the next code points indicate the beginning of an RDF* triple value, false otherwise
	 * @throws IOException
	 */
	protected boolean peekIsTripleValue() {
		int c0 = currentLine.charAt(currentIndex);
		if (currentIndex < currentLine.length() - 1) {
			int c1 = currentLine.charAt(currentIndex + 1);
			return c0 == '<' && c1 == '<';
		} else {
			return false;
		}
	}

	/**
	 * Parser an RDF* triple value and returns it.
	 *
	 * @return An RDF* triple.
	 * @throws IOException
	 */
	protected Triple parseTripleValue() throws IOException {
		verifyCharacterOrFail(currentLine.charAt(currentIndex), "<");
		verifyCharacterOrFail(readCodePoint(), "<");
		skipToNextIndex();
		skipMultilineWSC(true);
		Value subject = parseValue();
		if (subject instanceof Resource) {
			skipMultilineWSC(true);
			Value predicate = parseValue();
			if (predicate instanceof IRI) {
				skipMultilineWSC(true);
				Value object = parseValue();
				if (object != null) {
					skipMultilineWSC(true);
					verifyCharacterOrFail(currentLine.charAt(currentIndex), ">");
					verifyCharacterOrFail(readCodePoint(), ">");
					skipToNextIndex();
					skipMultilineWSC(true);
					return valueFactory.createTriple((Resource) subject, (IRI) predicate, object);
				} else {
					reportFatalError("Missing object in RDF* triple");
				}
			} else {
				reportFatalError("Illegal predicate value in RDF* triple: " + predicate);
			}
		} else {
			reportFatalError("Illegal subject val in RDF* triple: " + subject);
		}

		return null;
	}
}
