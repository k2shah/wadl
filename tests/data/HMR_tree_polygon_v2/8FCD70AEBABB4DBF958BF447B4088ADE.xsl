<?xml version="1.0" encoding="UTF-8"?>
<xsl:stylesheet version="1.0" xmlns:xsl="http://www.w3.org/1999/XSL/Transform" xmlns:fo="http://www.w3.org/1999/XSL/Format" xmlns:msxsl="urn:schemas-microsoft-com:xslt">
	<xsl:variable name="ignoreFieldNames" select="'|OBJECTID|Shape|Shape_Length|Shape_Area|ATTACHMENTID|REL_OBJECTID|CONTENT_TYPE|ATT_NAME|DATA_SIZE|DATA|'"/>
	<xsl:variable name="headerRowColor" select="'#9CBCE2'"/>
	<xsl:variable name="alternateRowColor" select="'#D4E4F3'"/>
	<xsl:template match="/">
		<html>
			<head>
				<meta http-equiv="content-type" content="text/html; charset=UTF-8"/>
			</head>
			<body style="margin:0px 0px 0px 0px;overflow:auto;background:#FFFFFF;">
				<table style="font-family:Arial,Verdana,Times;font-size:12px;text-align:left;width:100%;border-collapse:collapse;padding:3px 3px 3px 3px">
					<tr style="text-align:center;font-weight:bold;background:{$headerRowColor}">
						<td>
							<xsl:value-of select="FieldsDoc/Title" />
						</td>
					</tr>
					<xsl:apply-templates select="FieldsDoc/Attachments" />
					<tr>
						<td>
							<table style="font-family:Arial,Verdana,Times;font-size:12px;text-align:left;width:100%;border-spacing:0px; padding:3px 3px 3px 3px">
								<xsl:choose>
									<xsl:when test="FieldsDoc/Fields/Field/FieldName">
										<xsl:apply-templates select="FieldsDoc/Fields/Field/FieldName[not(contains($ignoreFieldNames, concat(concat('|', text()), '|')))]/.." />
									</xsl:when>
									<xsl:otherwise>
										<xsl:apply-templates select="FieldsDoc/Fields/Field" />
									</xsl:otherwise>
								</xsl:choose>
							</table>
						</td>
					</tr>
				</table>
			</body>
		</html>
	</xsl:template>

	<xsl:template match="Attachments">
		<xsl:variable name="imageCount" select="count(Attachment/ContentType[contains(., 'image')])"/>
		<xsl:variable name="attachmentCount" select="count(Attachment)"/>
		<tr bgcolor="{$headerRowColor}">
			<td>
				<table style="font-family:Arial,Verdana,Times;font-size:12px;text-align:left;width:100%;border-spacing:0px; padding:3px 3px 3px 3px">
					<xsl:variable name="imageSrc" select="Attachment/ContentType[contains(., 'image')]/../FilePath"/>
					<xsl:if test="$imageSrc">
						<tr align="center">
							<td>
								<a target="_blank" href="{$imageSrc}">
									<img src="{$imageSrc}" width="275px" border="0"/>
								</a>
							</td>
						</tr>
						<tr align="center">
							<td>
								<xsl:value-of select="Attachment/ContentType[contains(., 'image')]/../Name" />
							</td>
						</tr>
					</xsl:if>
					<xsl:if test="($attachmentCount &gt; $imageCount) or not($imageCount = 1)">
						<tr align="center">
							<td>
								<table style="font-family:Arial,Verdana,Times;font-size:12px;text-align:left;width:100%;border-spacing:0px; padding:3px 3px 3px 3px">
									<xsl:for-each select="Attachment[position() mod 2 = 1]">
										<tr align="left" bgcolor="white">
											<xsl:if test="(position() +1) mod 2">
												<xsl:attribute name="bgcolor">
													<xsl:value-of select="$alternateRowColor"/>
												</xsl:attribute>
											</xsl:if>
											<td>
												<a target="_blank">
													<xsl:attribute name="href">
														<xsl:value-of select="FilePath"/>
													</xsl:attribute>
													<xsl:value-of select="Name" />
												</a>
											</td>
											<td>
												<a target="_blank">
													<xsl:attribute name="href">
														<xsl:value-of select="following-sibling::Attachment/FilePath"/>
													</xsl:attribute>
													<xsl:value-of select="following-sibling::Attachment/Name" />
												</a>
											</td>
										</tr>
									</xsl:for-each>
								</table>
							</td>
						</tr>
					</xsl:if>
				</table>
			</td>
		</tr>
	</xsl:template>

	<xsl:template match="Field">
		<tr>
			<xsl:if test="(position() +1) mod 2">
				<xsl:attribute name="bgcolor">
					<xsl:value-of select="$alternateRowColor"/>
				</xsl:attribute>
			</xsl:if>
			<xsl:if test="FieldName">
				<td>
					<xsl:value-of select="FieldName"/>
				</td>
			</xsl:if>
			<td>
				<xsl:choose>
					<xsl:when test="FieldValue[starts-with(., 'www.')]">
						<a target="_blank">
							<xsl:attribute name="href">http://<xsl:value-of select="FieldValue"/>
							</xsl:attribute>
							<xsl:value-of select="FieldValue"/>
						</a>
					</xsl:when>
					<xsl:when test="FieldValue[starts-with(., 'http:')]">
						<a target="_blank">
							<xsl:attribute name="href">
								<xsl:value-of select="FieldValue"/>
							</xsl:attribute>
							<xsl:value-of select="FieldValue"/>
						</a>
					</xsl:when>
					<xsl:when test="FieldValue[starts-with(., 'https:')]">
						<a target="_blank">
							<xsl:attribute name="href">
								<xsl:value-of select="FieldValue"/>
							</xsl:attribute>
							<xsl:value-of select="FieldValue"/>
						</a>
					</xsl:when>
					<xsl:when test="FieldValue[starts-with(., '\\')]">
						<a target="_blank">
							<xsl:attribute name="href">
								<xsl:value-of select="FieldValue"/>
							</xsl:attribute>
							<xsl:value-of select="FieldValue"/>
						</a>
					</xsl:when>
					<xsl:when test="FieldValue[starts-with(., '&lt;img ')]">
						<xsl:value-of select="FieldValue" disable-output-escaping="yes" />
					</xsl:when>
					<xsl:otherwise>
						<xsl:value-of select="FieldValue"/>
					</xsl:otherwise>
				</xsl:choose>
			</td>
		</tr>
	</xsl:template>
</xsl:stylesheet>