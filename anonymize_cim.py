import argparse
import base64
from collections import Counter, defaultdict, deque
from concurrent.futures import ProcessPoolExecutor
from contextlib import nullcontext
from datetime import date, datetime
import functools
import hmac
import io
import ipaddress
from itertools import zip_longest
import json
import os
from pathlib import Path
import re
import secrets
import sqlite3
import sys
from tempfile import TemporaryDirectory
from time import perf_counter
import wave
from zipfile import BadZipFile, ZIP_DEFLATED, ZipFile, ZipInfo

from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes
from lxml import etree
from PIL import Image


RDF = '{http://www.w3.org/1999/02/22-rdf-syntax-ns#}'
RDF_IDS = {RDF + 'about', RDF + 'ID', RDF + 'nodeID'}
RDF_VALUE = RDF + 'resource'
XML_BASE = '{http://www.w3.org/XML/1998/namespace}base'
TECHNICAL_ATTRIBUTES = {RDF + 'datatype', RDF + 'parseType',
                        '{http://www.w3.org/XML/1998/namespace}lang'}
GUID = re.compile(r'[a-f0-9]{8}(?:-[a-f0-9]{4}){3}-[a-f0-9]{12}', re.I)
DECIMAL = re.compile(r'[0-9]+')
SCALAR = re.compile(
    r'(?i)(?:true|false|[+-]?(?:\d+(?:[.,]\d*)?|[.,]\d+)(?:e[+-]?\d+)?)'
)
PLACEHOLDER = re.compile(
    r'\{[0-9]+(?:,-?[0-9]+)?(?::[A-Za-z0-9.#%+ /:,\-]+)?\}|%[sdif]|\$\{[A-Za-z0-9_.]+\}'
)

PEOPLE = (
    ('Алёна', 'Алёнина', 'Алёновна', 'alena', 'Алёнина'),
    ('Вера', 'Верина', 'Веровна', 'vera', 'Верина'),
    ('Дарья', 'Дарьина', 'Дарьевна', 'darya', 'Дарьина'),
    ('Елена', 'Еленина', 'Еленовна', 'elena', 'Еленина'),
    ('Ирина', 'Иринина', 'Ириновна', 'irina', 'Иринина'),
    ('Лада', 'Ладина', 'Ладовна', 'lada', 'Ладина'),
    ('Антон', 'Антонов', 'Антонович', 'anton', 'Антонова'),
    ('Арсений', 'Арсеньев', 'Арсеньевич', 'arseniy', 'Арсеньева'),
    ('Борис', 'Борисов', 'Борисович', 'boris', 'Борисова'),
    ('Вадим', 'Вадимов', 'Вадимович', 'vadim', 'Вадимова'),
    ('Илья', 'Ильин', 'Ильич', 'ilya', 'Ильина'),
    ('Мирон', 'Миронов', 'Миронович', 'miron', 'Миронова'),
    ('Олег', 'Олегов', 'Олегович', 'oleg', 'Олегова'),
    ('Роман', 'Романов', 'Романович', 'roman', 'Романова'),
    ('Тимур', 'Тимуров', 'Тимурович', 'timur', 'Тимурова'),
    ('Яков', 'Яковлев', 'Яковлевич', 'yakov', 'Яковлева'),
)
PRODUCE = (
    ('абрикос', 'Абрикосовый'), ('ананас', 'Ананасовый'),
    ('апельсин', 'Апельсиновый'), ('баклажан', 'Баклажановый'),
    ('виноград', 'Виноградный'), ('гранат', 'Гранатовый'),
    ('груша', 'Грушевый'), ('кабачок', 'Кабачковый'),
    ('капуста', 'Капустный'), ('лимон', 'Лимонный'),
    ('морковь', 'Морковный'), ('персик', 'Персиковый'),
    ('редис', 'Редисовый'), ('слива', 'Сливовый'),
    ('тыква', 'Тыквенный'), ('яблоко', 'Яблочный'),
)

CLASS_LABELS = {
    'ACLineSegment': 'ЛЭП', 'Line': 'ЛЭП', 'ACLineSeriesSection': 'Участок ЛЭП',
    'PowerTransformer': 'Т', 'PowerTransformerEnd': 'Обмотка',
    'Substation': 'ПС', 'SubstationSLD': 'Схема ПС', 'Pole': 'Опора',
    'Bay': 'Присоединение', 'VoltageLevel': 'РУ', 'Breaker': 'Выключатель',
    'BusbarSection': 'Секция шин', 'Disconnector': 'Разъединитель',
    'ConnectivityNode': 'Узел', 'Terminal': 'Терминал', 'Meter': 'Счётчик',
    'DistributionSubstation': 'ТП', 'DistributionPoint': 'РП',
    'ServiceLocation': 'Точка обслуживания', 'Organisation': 'Организация',
    'Customer': 'Абонент', 'ModelingAuthoritySet': 'Модель',
}
PERSON_CLASSES = {'Person', 'Employee', 'Individual', 'NaturalPerson', 'StaffMember'}
PERSON_NAME_FIELDS = {
    'firstname', 'givenname', 'lastname', 'surname', 'familyname', 'middlename', 'patronymic',
}
PERSON_LABELS = {'fullname', 'fio', 'inchargefullname', 'contactname', 'ownername'}
PERSON_NAME = re.compile(r'[А-ЯЁ][а-яё-]+\s+[А-ЯЁ][а-яё-]+(?:\s+[А-ЯЁ][а-яё-]*(?:ич|ны|на))?')
TECHNICAL_TEXT = {
    'Asset.type', 'BasicIntervalSchedule.points', 'CalendarDay.date',
    'CurrentTransformer.accuracyClass', 'CurrentTransformer.ctClass',
    'CurrentTransformer.ioptsat', 'CurrentTransformer.it2p2', 'CurrentTransformer.it2pl',
    'CurrentTransformer.pbranch', 'Curve.points', 'DocumentType.contentType',
    'DocumentType.fileExtension', 'InUseDate.inUseDate', 'Model.created', 'Model.version',
    'PSRType.className', 'PSRType.prefix', 'RatioTapChangerTable.points', 'Season.endDate',
    'Season.startDate', 'SensorWinding.accuracyClass', 'Shift.endTime', 'Shift.startTime',
    'VCTimeSpan.endTime', 'VCTimeSpan.startTime', 'VCValidityPeriod.endDate',
    'VCValidityPeriod.startDate',
}
IDENTIFIER_FIELDS = {
    'mrid', 'mridstr', 'fiasid', 'fiasstreetid', 'serialnumber', 'inventorynumber',
    'inventoryno', 'personnelnumber', 'employeeid', 'staffnumber', 'taxid',
    'inn', 'kpp', 'ogrn', 'snils', 'passport', 'passportnumber', 'passportseries',
    'contract', 'contractnumber', 'agreementnumber', 'accountnumber',
    'personalaccount', 'licence', 'licensenumber', 'taxregistrationnumber',
    'meteringpointcode', 'ccscode', 'nameplate', 'dispatchnumber',
    'inventorycode', 'registrationnumber', 'documentnumber', 'taxnumber',
    'identificationnumber', 'customernumber', 'nationalid', 'idnumber',
    'postalcode', 'postcode', 'zipcode', 'companynumber', 'commonaddress',
    'addrstr1', 'buildingnumber', 'apartmentnumber', 'pobox',
    'suitenumber',
    'tabnumber', 'taxpayerid', 'policynumber', 'omsnumber',
    'accountid', 'contractid', 'meterid', 'subscriberid', 'billingaccount',
    'dispatchcode', 'cadastralnumber', 'objectnumber', 'meterreading', 'readingvalue',
    'bankaccountnumber', 'bik', 'korrschet', 'personid', 'birthcertificate',
}
MASK_FIELDS = {
    'description', 'comment', 'comments', 'notes', 'note', 'remark', 'remarks',
    'log', 'logtext', 'message', 'text', 'markertext', 'djrecordtext',
    'texttemplate', 'signature', 'username', 'login', 'password',
    'birthdate', 'dateofbirth', 'issuedby', 'passportissuer', 'website', 'url',
    'filename', 'filepath', 'attachment', 'attachmentdata',
    'personaldata', 'biography', 'attachmentname', 'logentry', 'content',
}
ADDRESS_FIELDS = {
    'address', 'addressgeneral', 'country', 'stateorprovince', 'city',
    'town', 'buildingname', 'street', 'district', 'county', 'addressline',
    'addressline1', 'addressline2', 'postaladdress', 'registeredaddress',
}
DIAGRAM_LABELS = {
    'description', 'name', 'text', 'elementname', 'itemname', 'caption',
    'label', 'tooltip', 'header', 'title', 'tag', 'comment', 'address',
}
DIAGRAM_REFERENCE_TEXT = {
    'powersystemresource', 'measurementtype', 'measurementvalue',
    'valuetype', 'specifiedterminal', 'uid',
}
DIAGRAM_PRIVATE_LABELS = {
    'username', 'stringofnames', 'author', 'rulename', 'login', 'fullname',
}
DIAGRAM_VALUE_LABELS = {'node', 'parameter1', 'parameter2', 'elementproperty', 'unitproperty'}
DIAGRAM_TECHNICAL_TEXT = {'height', 'width', 'field'}
NIL_UUID = '00000000-0000-0000-0000-000000000000'
DIAGRAM_SYMBOLS = {
    ('textstyle', 'name'), ('strokestyle', 'name'), ('prop', 'name'), ('link', 'itemname'),
}
DIAGRAM_TERMINALS = {
    ('psrterminal', 'name'), ('tsterminal', 'name'), ('connectedorigin', 'terminal'),
    ('connecteddestination', 'terminal'), ('familiar', 'terminal'),
}
LOCAL_REFERENCE = re.compile(r'(?:#_?|urn:uuid:|_)?(' + GUID.pattern + r')\Z', re.I)
SAFE_MEMBER = re.compile(
    r'(?:\[Content_Types\]\.xml|(?:[\w.-]+/)*(?:\.rels|[\w.-]+\.(?:xml|rels|png|bmp|jpe?g|gif|ico|scrap)))\Z', re.I
)
COORDS = {'latitude', 'longitude', 'xposition', 'yposition', 'zposition', 'coordinates'}
ZIP_EXPANDED_LIMIT = 256 * 1024 * 1024
ZIP_MEMBER_LIMIT = 16_384
PENDING_DIAGRAM_BYTES = 32 * 1024 * 1024
NAMESPACE_DECLARATION = rb' xmlns(?::[^\s=]+)?="[^"]*"'
OPEN_TAG = re.compile(rb'(<[^\s/>]+)((?:' + NAMESPACE_DECLARATION + rb')*)')
NAMESPACE_ATTRIBUTE = re.compile(NAMESPACE_DECLARATION)
SAFE_PI = {'iec61970-552': 'version="2.0"', 'floatExporter': '1'}
SCHEMA_URIS = (
    'http://iec.ch/TC57/', 'http://monitel.com/2014/schema-cim16#',
    'http://gost.ru/2019/schema-cim01#', 'http://rushydro.ru/2015/schema-cim16#',
    'http://so-ups.ru/2015/schema-cim16#', 'http://www.w3.org/1999/02/22-rdf-syntax-ns#',
)
SCHEMA_SYMBOL = re.compile(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*')
URI_SCHEME = re.compile(r'[a-z][a-z0-9+.-]*:', re.I)
STATION_TYPE = re.compile(r'(?<![А-ЯЁ])(?:БКТП|КТПН|КТП|РТП|ТП|РП)(?![А-ЯЁ])', re.I)
EQUIPMENT_NUMBER = re.compile(r'(?:ЛЭП|БКТП|КТПН|КТП|РТП|ТП|ПС|РП)[\s№-]*([0-9]+)(?![0-9.,])', re.I)
FORMULA_FIELDS = {'Expression.formula', 'FormulaTemplate.formula'}
OPERAND_OWNER = {'Operand.Expression', 'BaseTemplateOperand.ExpressionTemplate'}
FORMULA_SYMBOL = re.compile(r'(?<![\w.])[^\W\d]\w*')
DIAGRAM_FORMULA_TOKEN = re.compile(
    GUID.pattern + r'|"[^"\r\n]*"|\'[^\'\r\n]*\'|\b[^\W\d]\w*', re.I,
)
DIAGRAM_SCRIPT_TOKEN = re.compile(
    r'(?P<comment>//[^\r\n]*|/\*[\s\S]*?\*/)'
    r'|(?P<string>\$?@"(?:[^"]|"")*"|@?\$?"(?:[^"\\]|\\.)*"|\'(?:[^\'\\]|\\.)*\')'
    r'|(?P<uuid>' + GUID.pattern + ')', re.I,
)
CYRILLIC = re.compile(r'[А-Яа-яЁё]')
CYRILLIC_SCRIPT_TEXT = re.compile(r'[А-Яа-яЁё]+(?:[ \t]+[А-Яа-яЁё]+)*')


@functools.lru_cache(maxsize=4096)
def local(tag):
    return tag.rsplit('}', 1)[-1]


@functools.lru_cache(maxsize=4096)
def field_parts(prop):
    owner, _, field = prop.rpartition('.')
    lower = re.sub(r'[^a-z0-9]', '', field.lower())
    is_phone = any(part in lower for part in ('phone', 'mobile', 'fax', 'telephone'))
    return owner, lower, is_phone


def rdf_key(value, attribute):
    if attribute == RDF + 'nodeID':
        return '_:' + value
    if attribute == RDF + 'ID':
        return '#' + value
    return value


def object_identity(record):
    about = record.get(RDF + 'about')
    if about is not None and len(record.attrib) == 1:
        return about
    return next((rdf_key(value, key) for key, value in record.attrib.items() if key in RDF_IDS), '')


def schema_reference(value, node):
    if value.startswith(SCHEMA_URIS):
        return bool(SCHEMA_SYMBOL.fullmatch(value.rsplit('#', 1)[-1]))
    prefix, _, symbol = value.partition(':')
    if not SCHEMA_SYMBOL.fullmatch(symbol):
        return False
    return node.nsmap.get(prefix, '').startswith(SCHEMA_URIS)


def local_reference(value):
    return not URI_SCHEME.match(value) or bool(LOCAL_REFERENCE.fullmatch(value))


def select_key(path, create):
    if create:
        try:
            with path.open('xb') as stream:
                stream.write(secrets.token_bytes(32))
        except FileExistsError:
            pass
    key = path.read_bytes()
    if len(key) != 32:
        raise ValueError('The key file must contain exactly 32 bytes.')
    return key


class Pseudonyms:
    def __init__(self, key, ref_cache_size=200_000, translations=None):
        self.key = key
        self.translations = translations if translations is not None else {}
        permutation = Cipher(algorithms.AES(self.digest('rdf', 'v1')), modes.ECB())
        self.encrypt = permutation.encryptor()
        self.decrypt = permutation.decryptor()
        self.guid = functools.lru_cache(maxsize=16_384)(self.guid)
        self.ref = functools.lru_cache(maxsize=ref_cache_size)(self.ref)
        self.identifier = functools.lru_cache(maxsize=50_000)(self.identifier)
        self.decimal = functools.lru_cache(maxsize=32_768)(self.decimal)

    def digest(self, domain, text):
        return hmac.digest(self.key, (domain + '\0' + text).encode('utf-8'), 'sha256')

    def guid(self, value):
        raw = bytes.fromhex(value.replace('-', ''))
        block = self.encrypt.update(raw)
        changed = block[:-1] + bytes([block[-1] ^ 1])
        encoded = self.decrypt.update(changed).hex()
        return f'{encoded[:8]}-{encoded[8:12]}-{encoded[12:16]}-{encoded[16:20]}-{encoded[20:]}'

    def ref(self, value):
        if match := LOCAL_REFERENCE.fullmatch(value):
            return value[:match.start(1)] + self.guid(match[1].lower())
        if URI_SCHEME.match(value):
            return 'urn:cim-anonymized:' + self.token('absolute-rdf-id', value, length=20)
        prefix = '#' if value.startswith('#') else ''
        return prefix + 'anon_' + self.token('rdf-id', value.removeprefix('#'), length=20)

    def token(self, domain, value, length=12):
        return base64.b32encode(self.digest(domain, value)[:length]).decode('ascii').rstrip('=')

    def person(self, value):
        first, last, patronymic, spelling, street = PEOPLE[self.digest('person', value)[0] % len(PEOPLE)]
        return self.translate(first), self.translate(last), self.translate(patronymic), spelling, self.translate(street)

    def translate(self, value):
        return self.translations.get(value, value)

    def adjective(self, value):
        return PRODUCE[self.digest('produce', value)[0] % len(PRODUCE)][1]

    def label(self, value, prefix='', identity=None):
        suffix = self.token('object-label', identity) if identity else self.token('label', value)
        adjective = self.adjective(value)
        if prefix in {'ПС', 'ТП', 'ЛЭП', 'Опора', 'Секция шин', 'Обмотка'}:
            adjective = adjective[:-2] + 'ая'
        number = EQUIPMENT_NUMBER.search(value) if prefix in {'ПС', 'ТП', 'РП', 'ЛЭП'} else None
        synthetic = f'{self.translate(adjective)} {suffix}'
        if number:
            synthetic += f' №{self.decimal(number[1])}'
        return f'{self.translate(prefix)} {synthetic}' if prefix else synthetic

    def full_name(self, seed, unique=False):
        first, last, patronymic, _, _ = self.person(seed)
        name = f'{last} {first} {patronymic}'
        return f'{name} ({self.token("person-label", seed)})' if unique else name

    def formula_symbol(self, seed):
        return 'V_' + self.token('formula-symbol', seed)

    def date(self, value):
        try:
            original = date.fromisoformat(value[:10])
        except ValueError:
            return self.identifier(value)
        days = 365 * 10
        offset = 1 + int.from_bytes(self.digest('personal-date', value)[:4], 'big') % days
        ordinal = (original.toordinal() - 1 + offset) % date.max.toordinal() + 1
        date_part = date.fromordinal(ordinal).isoformat()
        if len(value) == 10:
            return date_part
        try:
            datetime.fromisoformat(value)
        except ValueError:
            return self.identifier(value)
        return date_part + value[10:11] + '00:00:00Z'

    def decimal(self, value):
        width = len(value)
        if width == 1:
            offset = 1 + self.digest('digit', 'v1')[0] % 9
            return str((int(value) + offset) % 10)
        widths = (width // 2, width - width // 2)
        limits = tuple(10 ** count for count in widths)

        def mix(round_number, digit_string):
            scope = f'decimal:{width}:{round_number}'
            return int.from_bytes(self.digest(scope, digit_string), 'big')

        left, right = int(value[:widths[0]]), int(value[widths[0]:])
        for step in range(8):
            side = step % 2
            if side == 0:
                left = (left + mix(step, str(right))) % limits[0]
            else:
                right = (right + mix(step, str(left))) % limits[1]
        right ^= 1
        for step in reversed(range(8)):
            side = step % 2
            if side == 0:
                left = (left - mix(step, str(right))) % limits[0]
            else:
                right = (right - mix(step, str(left))) % limits[1]
        return str(left).zfill(widths[0]) + str(right).zfill(widths[1])

    def identifier(self, value):
        if LOCAL_REFERENCE.fullmatch(value):
            return self.ref(value)
        if DECIMAL.fullmatch(value):
            return self.decimal(value)
        groups = DECIMAL.findall(value)
        suffix = '-' + '-'.join(self.decimal(group) for group in groups) if groups else ''
        return 'ID-' + self.token('identifier', value) + suffix

    def free_text(self, value):
        placeholders = PLACEHOLDER.findall(value)
        result = self.label(value)
        if placeholders:
            result += ' ' + ' '.join(placeholders)
        return result

    def embedded_refs(self, value):
        return GUID.sub(lambda match: self.guid(match[0].lower()), value)


def parser_for_embedded():
    return etree.XMLParser(
        resolve_entities=False, no_network=True, load_dtd=False, remove_comments=True,
        remove_pis=True,
    )


def diagram_formula(node, value, pseudonyms):
    expression = node.getparent()
    operands = {
        name for operand in expression.iterdescendants('{*}Operand')
        if (name := operand.get('Name')) and FORMULA_SYMBOL.fullmatch(name)
    } if expression is not None else set()

    def replace(match):
        token = match[0]
        if GUID.fullmatch(token):
            return pseudonyms.guid(token.lower())
        if token in operands:
            return pseudonyms.formula_symbol(token)
        return pseudonyms.embedded_refs(token)

    return DIAGRAM_FORMULA_TOKEN.sub(replace, value)


def diagram_script(value, pseudonyms):
    def replace(match):
        token = match[0]
        if match.lastgroup == 'comment':
            if token.startswith('//'):
                return '//'
            return '/*' + ''.join(re.findall(r'[\r\n]', token)) + '*/'
        mapped = pseudonyms.embedded_refs(token)
        if match.lastgroup == 'string' and token.startswith(('"', '@"')):
            return CYRILLIC_SCRIPT_TEXT.sub(lambda item: pseudonyms.formula_symbol(item[0]), mapped)
        return mapped

    return DIAGRAM_SCRIPT_TOKEN.sub(replace, value)


def diagram_attribute(tag, field, value, pseudonyms):
    if field == 'currentexpression' or (tag == 'lexpression' and field == 'name'):
        return 'E_' + pseudonyms.token('diagram-expression', value)
    if tag == 'operand' and field == 'name':
        if FORMULA_SYMBOL.fullmatch(value):
            return pseudonyms.formula_symbol(value)
        return pseudonyms.embedded_refs(value)
    if field in DIAGRAM_PRIVATE_LABELS:
        if field == 'stringofnames':
            return ''.join(pseudonyms.free_text(part) if part.strip() and not re.fullmatch(r'[;\r\n]+', part)
                           else part for part in re.split(r'([;\r\n]+)', value))
        return pseudonyms.free_text(value)
    if (tag, field) in DIAGRAM_TERMINALS:
        return value if DECIMAL.fullmatch(value) else pseudonyms.identifier(value)
    if (tag, field) in DIAGRAM_SYMBOLS:
        return pseudonyms.embedded_refs(value)
    if field in DIAGRAM_LABELS:
        return pseudonyms.free_text(value)
    if field == 'value' and tag in DIAGRAM_VALUE_LABELS and CYRILLIC.search(value):
        return pseudonyms.free_text(value)
    return pseudonyms.embedded_refs(value)


def embedded_xml(data, pseudonyms, diagram=False, sections=False):
    root = etree.fromstring(data, parser_for_embedded())
    if root.getroottree().docinfo.doctype:
        raise ValueError('DOCTYPE in embedded XML.')
    if diagram:
        for node in root.iter('{*}Formula'):
            if node.text and node.text.strip():
                node.text = diagram_formula(node, node.text, pseudonyms)
    for node in root.iter():
        tag = local(node.tag).lower()
        for key, value in node.attrib.items():
            field = local(key).lower()
            if not value.strip():
                continue
            if tag == 'relationship' and field == 'target' and node.get('TargetMode') == 'External':
                node.set(key, 'about:blank')
            elif sections and field == 'nameplate':
                node.set(key, pseudonyms.identifier(value))
            elif sections and field == 'name':
                node.set(key, pseudonyms.label(value, 'Участок ЛЭП'))
            elif diagram:
                node.set(key, diagram_attribute(tag, field, value, pseudonyms))
            elif field in {'description', 'comment', 'address'}:
                node.set(key, pseudonyms.free_text(value))
            else:
                node.set(key, pseudonyms.embedded_refs(value))
        if node.text and (value := node.text.strip()):
            if diagram and (tag == 'formula' or tag in DIAGRAM_TECHNICAL_TEXT):
                pass
            elif diagram and tag == 'script':
                node.text = diagram_script(node.text, pseudonyms)
            elif diagram and tag in DIAGRAM_REFERENCE_TEXT and value.lower() == NIL_UUID:
                pass
            elif diagram and (tag in DIAGRAM_REFERENCE_TEXT or LOCAL_REFERENCE.fullmatch(value) or SCALAR.fullmatch(value)):
                node.text = pseudonyms.embedded_refs(node.text)
            elif diagram or tag in DIAGRAM_LABELS:
                node.text = pseudonyms.free_text(node.text)
            else:
                node.text = pseudonyms.embedded_refs(node.text)
        if node.tail and node.tail.strip():
            node.tail = pseudonyms.free_text(node.tail)
    return etree.tostring(root, encoding='UTF-8', xml_declaration=True)


def raster_placeholder(data):
    with Image.open(io.BytesIO(data)) as image:
        image_format = image.format
    output = io.BytesIO()
    color = (255, 255, 255)
    size = (32, 32) if image_format == 'ICO' else (1, 1)
    Image.new('RGB', size, color).save(output, format=image_format)
    return output.getvalue()


def diagram_archive(data, pseudonyms, depth=0, *, compression_level=None, budget=None):
    if depth > 4:
        raise ValueError('Excessive nesting in diagram package.')
    if budget is None:
        budget = [ZIP_MEMBER_LIMIT, ZIP_EXPANDED_LIMIT]
    output = io.BytesIO()
    with ZipFile(io.BytesIO(data)) as original, ZipFile(output, 'w') as sanitized:
        members = original.infolist()
        budget[0] -= len(members)
        budget[1] -= sum(member.file_size for member in members)
        if min(budget) < 0:
            raise ValueError('Diagram package exceeds its unpacking budget.')
        seen = set()
        for member in members:
            name = member.filename
            if (not SAFE_MEMBER.fullmatch(name) or '..' in name.split('/') or name in seen
                    or member.file_size > 64 * 1024 * 1024):
                raise ValueError('Unexpected member in diagram package.')
            seen.add(name)
            content = original.read(member)
            if name.lower().endswith('.scrap'):
                content = diagram_archive(content, pseudonyms, depth + 1,
                                          compression_level=compression_level, budget=budget)
            elif name.lower().endswith(('.xml', '.rels')):
                diagram = name.lower().endswith('.xml') and name != '[Content_Types].xml'
                content = embedded_xml(content, pseudonyms, diagram=diagram)
            else:
                content = raster_placeholder(content)
            info = ZipInfo(name, date_time=(1980, 1, 1, 0, 0, 0))
            sanitized.writestr(info, content, compress_type=ZIP_DEFLATED, compresslevel=compression_level)
    return output.getvalue()


def anonymize_diagram(value, pseudonyms, compression_level):
    archive = diagram_archive(base64.b64decode(value), pseudonyms, compression_level=compression_level)
    return base64.b64encode(archive).decode('ascii')


def prepare_diagram_worker(key, compression_level, translations):
    global process_diagram
    pseudonyms = Pseudonyms(key, translations=translations)
    process_diagram = functools.partial(anonymize_diagram, pseudonyms=pseudonyms,
                                        compression_level=compression_level)


def run_diagram_worker(value):
    return process_diagram(value)


def silence():
    output = io.BytesIO()
    with wave.open(output, 'wb') as sound:
        sound.setparams((1, 2, 8000, 0, 'NONE', 'not compressed'))
        sound.writeframes(b'\0' * 1600)
    return base64.b64encode(output.getvalue()).decode('ascii')


class Transformer:
    def __init__(self, key, coordinates=False, catalog=None, *, ref_cache_size=200_000,
                 diagram_compression_level=None, translations=None):
        self.pseudonyms = Pseudonyms(key, ref_cache_size, translations)
        self.diagram_compression_level = diagram_compression_level
        self.diagram_seconds = 0.0
        self.coordinates = coordinates
        self.stats = Counter()
        self.classes = Counter()
        self.index = None
        self.catalog = catalog or ModelCatalog()

    def linked_name(self, target, value):
        linked = self.catalog.named_targets.get(target)
        if linked is None or linked[1] != value:
            return None
        cls, _, direct_kind, kind_ref = linked
        individual = cls in PERSON_CLASSES or (
            cls == 'Customer' and self.catalog.is_individual(direct_kind, kind_ref, value)
        )
        return self.literal('IdentifiedObject.name', cls, individual, target, value)

    def record(self, record, submit_diagram=None):
        etree.strip_elements(record, etree.ProcessingInstruction, with_tail=False)
        object_class = local(record.tag)
        self.classes[record.tag] += 1
        identity = object_identity(record)
        name_target = next(
            (child.get(RDF_VALUE) for child in record if local(child.tag) == 'Name.IdentifiedObject'),
            None,
        ) if object_class == 'Name' else None
        individual = object_class in PERSON_CLASSES
        if object_class == 'Customer':
            customer_kind = next(
                (child.get(RDF_VALUE, '') for child in record if local(child.tag) == 'Customer.kind'), ''
            )
            kind_ref = next(
                (child.get(RDF_VALUE, '') for child in record if local(child.tag) == 'Customer.OMSKind'), ''
            )
            name = next((child.text for child in record if local(child.tag) == 'IdentifiedObject.name'), '') or ''
            individual = self.catalog.is_individual(customer_kind, kind_ref, name)
            self.stats['customer_' + ('individual' if individual else 'other_or_unspecified')] += 1

        for node in record.iter():
            for attribute, value in node.attrib.items():
                if attribute == XML_BASE:
                    raise ValueError('xml:base is not supported for this CIM profile')
                if attribute in RDF_IDS:
                    mapped = self.pseudonyms.ref(value)
                    node.set(attribute, mapped)
                    self.stats['definitions'] += 1
                    if self.index is not None and (node is record or attribute != RDF + 'nodeID'):
                        self.index.definition(rdf_key(value, attribute), rdf_key(mapped, attribute))
                elif attribute == RDF_VALUE:
                    if value and not (':' in value and schema_reference(value, node)):
                        mapped = self.pseudonyms.ref(value)
                        node.set(attribute, mapped)
                        self.stats['references'] += 1
                        if self.index is not None:
                            self.index.reference(value, mapped, local_reference(value))
                    else:
                        self.stats['schema_references'] += 1
                elif value.strip() and attribute not in TECHNICAL_ATTRIBUTES:
                    node.set(attribute, self.literal(local(attribute), object_class, individual, identity, value))
            if node.text and node.text.strip():
                value = node.text.strip()
                prop = local(node.tag)
                if submit_diagram is not None and prop == 'MonitelDiagram.image':
                    self.stats['diagram_packages'] += 1
                    submit_diagram(node, value)
                else:
                    linked = self.linked_name(name_target, value) if name_target and prop == 'Name.name' else None
                    replaced = linked if linked is not None else self.literal(prop, object_class, individual, identity, value)
                    if replaced != value:
                        self.stats['modified_literals'] += 1
                        node.text = replaced
                    if self.index is not None and prop == 'IdentifiedObject.name':
                        self.index.name(replaced, identity or value)
            if node is not record and node.tail and node.tail.strip():
                node.tail = self.pseudonyms.free_text(node.tail.strip())

    def literal(self, prop, cls, individual, identity, value):
        p = self.pseudonyms
        owner, lower, is_phone = field_parts(prop)
        if prop == 'MonitelDiagram.image':
            started = perf_counter()
            self.stats['diagram_packages'] += 1
            encoded = anonymize_diagram(value, p, self.diagram_compression_level)
            self.diagram_seconds += perf_counter() - started
            return encoded
        if prop in {'BlobStorage.image', 'MarkerType.diagramView', 'MarkerType.additionalView'}:
            self.stats['raster_attachments'] += 1
            return base64.b64encode(raster_placeholder(base64.b64decode(value))).decode('ascii')
        if prop == 'EventSound.sound':
            self.stats['audio_attachments'] += 1
            return silence()
        if prop in {'ACLineSegment.sections', 'DjCategory.allowedObjectsFilter', 'DjAttributeSet.xsd'}:
            self.stats['encoded_xml'] += 1
            data = embedded_xml(base64.b64decode(value), p, sections=prop == 'ACLineSegment.sections')
            return base64.b64encode(data).decode('ascii')
        if prop == 'IdentifiedObject.name':
            if identity in self.catalog.operands:
                return p.formula_symbol(identity)
            if individual:
                return p.full_name(identity or value, unique=True)
            prefix = CLASS_LABELS.get(cls, '')
            if cls == 'Substation':
                match = STATION_TYPE.search(value.upper())
                if match:
                    prefix = 'РП' if match[0] == 'РП' else 'ТП'
            return p.label(value, prefix, identity)
        if lower in PERSON_LABELS:
            return p.full_name((identity if individual else '') or value)
        if lower in PERSON_NAME_FIELDS:
            first, last, patronymic, _, _ = p.person(identity or value)
            if lower in {'firstname', 'givenname'}:
                return first
            return last if lower in {'lastname', 'surname', 'familyname'} else patronymic
        if 'email' in lower or lower in {'mail', 'emailaddress'}:
            _, _, _, spelling, _ = p.person(identity or value)
            return f'{spelling}.{p.token("email", value).lower()}@example.invalid'
        if is_phone:
            return re.sub(r'[0-9]+', lambda match: p.decimal(match[0]), value) if re.fullmatch(r'[+()0-9 .-]+', value) else p.identifier(value)
        if prop == 'StreetDetail.name' or lower in {'streetname', 'street'}:
            _, _, _, _, street = p.person((identity if individual else '') or value)
            return f'ул. {street} {p.token("street", value)}'
        if owner in {'StreetDetail', 'TownDetail', 'PostalAddress', 'StreetAddress', 'Address'}:
            return p.identifier(value) if lower in IDENTIFIER_FIELDS | {'number'} or DECIMAL.fullmatch(value) else p.label(value)
        if prop == 'IPConnectionPoint.address':
            try:
                address = ipaddress.ip_address(value)
            except ValueError:
                return p.label(value)
            code = int.from_bytes(p.digest('ip-address', value)[:8], 'big')
            if address.version == 4:
                networks = ('192.0.2.', '198.51.100.', '203.0.113.')
                return networks[code % 3] + str(1 + code // 3 % 254)
            return str(ipaddress.IPv6Address(int(ipaddress.IPv6Address('2001:db8::')) | code))
        if lower in ADDRESS_FIELDS:
            return p.label(value)
        if owner in {'Attachment', 'DocumentAttachment'} and lower in {'data', 'content', 'attachmentdata'}:
            return base64.b64encode(b'REDACTED').decode('ascii')
        if owner in {'MeterReading', 'Reading', 'IntervalReading'} and lower in {'value', 'reading'}:
            return re.sub(r'[0-9]+', lambda match: p.decimal(match[0]), value) if SCALAR.fullmatch(value) else p.identifier(value)
        if lower in IDENTIFIER_FIELDS:
            return p.identifier(value)
        if lower in COORDS:
            if not self.coordinates:
                return value
            return '0' if SCALAR.fullmatch(value) else p.free_text(value)
        if lower in {'birthdate', 'dateofbirth', 'dob', 'passportissuedate'}:
            return p.date(value)
        if lower in MASK_FIELDS or lower.endswith(('password', 'signature', 'comment', 'logentry')):
            return p.free_text(value)
        if ('name' in lower and prop != 'PSRType.className') or lower == 'designation':
            if individual:
                return p.full_name(identity or value)
            return p.label(value)
        if prop in FORMULA_FIELDS:
            return self.formula(identity, value)
        if prop == 'HISPartitionBase.prefix':
            return p.embedded_refs(value)
        if prop in TECHNICAL_TEXT or SCALAR.fullmatch(value):
            return value
        return p.free_text(value)

    def formula(self, identity, value):
        names = self.catalog.symbols.get(identity, {})
        pseudonyms = self.pseudonyms

        def replace(match):
            symbol = match[0]
            operand = names.get(symbol) or names.get(symbol.casefold())
            if operand:
                self.stats['formula_operand_mentions'] += 1
                return pseudonyms.formula_symbol(operand)
            if CYRILLIC.search(symbol):
                self.stats['other_cyrillic_formula_symbols'] += 1
                return pseudonyms.formula_symbol(symbol.casefold())
            return symbol

        return pseudonyms.embedded_refs(FORMULA_SYMBOL.sub(replace, value))


def open_rdf(path):
    reader = etree.iterparse(
        path, events=('start', 'end'), no_network=True, load_dtd=False,
        resolve_entities=False, remove_comments=True,
    )
    event, root = next(reader)
    if event != 'start' or root.tag != RDF + 'RDF':
        raise ValueError('Expected an rdf:RDF document.')
    if root.getroottree().docinfo.doctype:
        raise ValueError('DOCTYPE is not supported.')
    if XML_BASE in root.attrib:
        raise ValueError('xml:base is not supported for this CIM profile.')
    return root, reader


def records(root, reader, *, retain=False):
    for event, node in reader:
        if event != 'end' or node.getparent() is not root:
            continue
        yield node
        if not retain:
            discard_record(root, node)


def discard_record(root, node):
    node.clear()
    while node.getprevious() is not None:
        del root[0]


class ModelCatalog:
    def __init__(self):
        self.customer_kinds = {}
        self.operands = set()
        self.symbols = defaultdict(dict)
        self.named_targets = {}

    def remember_name(self, record, object_class, identity, name=None):
        if name is None:
            node = next(record.iterchildren('{*}IdentifiedObject.name'), None)
            name = (node.text or '').strip() if node is not None else ''
        if name:
            kinds = {local(node.tag): node.get(RDF_VALUE, '') for node in record
                     if local(node.tag) in {'Customer.kind', 'Customer.OMSKind'}} if object_class == 'Customer' else {}
            self.named_targets[identity] = (object_class, name, kinds.get('Customer.kind', ''),
                                            kinds.get('Customer.OMSKind', ''))

    def is_individual(self, direct_kind, kind_ref, name):
        kind = direct_kind.lower().rsplit('.', 1)[-1]
        if kind:
            return kind in {'residential', 'individual', 'naturalperson', 'household'}
        return self.customer_kinds.get(kind_ref, bool(PERSON_NAME.fullmatch(name.strip())))

    @classmethod
    def scan(cls, source):
        root, reader = open_rdf(source)
        result = cls()
        name_targets = set()
        seen_named_targets = set()
        for record in records(root, reader):
            object_class = local(record.tag)
            if object_class == 'Name':
                name_targets.update(target for node in record.iterchildren('{*}Name.IdentifiedObject')
                                    if (target := node.get(RDF_VALUE)))
            indexed = object_class == 'OMSCustomerKind' or object_class.endswith('Operand')
            linked = next(record.iterchildren('{*}IdentifiedObject.Names'), None) is not None
            if not indexed and not linked:
                continue
            identity = object_identity(record)
            if linked and identity:
                seen_named_targets.add(identity)
            name_node = next(record.iterchildren('{*}IdentifiedObject.name'), None)
            name = (name_node.text or '') if name_node is not None else ''
            if not identity or not name.strip():
                continue
            if linked:
                result.remember_name(record, object_class, identity, name.strip())
            if not indexed:
                continue
            if object_class == 'OMSCustomerKind':
                normalized = ' '.join(re.findall(r'[^\W_]+', name.casefold()))
                result.customer_kinds[identity] = any(part in normalized for part in (
                    'физическ', 'физ лиц', 'физлиц', 'населени', 'бытов',
                    'residential', 'natural person', 'individual',
                ))
                continue
            owner = next((node.get(RDF_VALUE) for node in record
                          if isinstance(node.tag, str) and local(node.tag) in OPERAND_OWNER), None)
            if owner:
                result.operands.add(identity)
                names = result.symbols[owner]
                names[name.strip()] = identity
                names.setdefault(name.strip().casefold(), identity)
        missing = name_targets - seen_named_targets
        if missing:
            root, reader = open_rdf(source)
            for record in records(root, reader):
                identity = object_identity(record)
                if identity in missing:
                    result.remember_name(record, local(record.tag), identity)
                    missing.remove(identity)
                    if not missing:
                        break
        return result


def header_instructions(root):
    instructions = []
    sibling = root.getprevious()
    while sibling is not None:
        if isinstance(sibling, etree._ProcessingInstruction) and SAFE_PI.get(sibling.target) == sibling.text:
            instructions.append(sibling)
        sibling = sibling.getprevious()
    return reversed(instructions)


class RdfWriter:
    def __init__(self, stream, root):
        self.stream = stream
        header = etree.tostring(etree.Element(root.tag, root.attrib, nsmap=root.nsmap), encoding='UTF-8')
        opening = OPEN_TAG.match(header)
        self.inherited = frozenset(NAMESPACE_ATTRIBUTE.findall(opening[2]))
        self.local_declarations = functools.lru_cache(maxsize=128)(self.local_declarations)
        self.closing = b'</' + opening[1][1:] + b'>\n'
        stream.write(b"<?xml version='1.0' encoding='UTF-8'?>\n")
        for instruction in header_instructions(root):
            stream.write(etree.tostring(instruction, encoding='UTF-8', with_tail=False))
        stream.write(header[:-2] + b'>\n')

    def local_declarations(self, declarations):
        return b''.join(item for item in NAMESPACE_ATTRIBUTE.findall(declarations)
                        if item not in self.inherited)

    def record(self, node):
        data = etree.tostring(node, encoding='UTF-8', with_tail=False)
        opening = OPEN_TAG.match(data)
        self.stream.write(opening[1] + self.local_declarations(opening[2]))
        self.stream.write(memoryview(data)[opening.end():])
        self.stream.write(b'\n')


def transform(source, destination, transformer, diagram_workers=1):
    started = perf_counter()
    anonymize_seconds = write_seconds = 0.0
    root, reader = open_rdf(source)
    if set(root.attrib) - TECHNICAL_ATTRIBUTES:
        raise ValueError('Unexpected attribute on the rdf:RDF root.')
    pool = (ProcessPoolExecutor(max_workers=diagram_workers, initializer=prepare_diagram_worker,
                               initargs=(transformer.pseudonyms.key, transformer.diagram_compression_level,
                                         transformer.pseudonyms.translations))
            if diagram_workers > 1 else nullcontext())
    with pool as executor, destination.open('wb', buffering=1024 * 1024) as stream:
        writer = RdfWriter(stream, root)
        pending = deque()
        pending_bytes = 0

        def write_next():
            nonlocal anonymize_seconds, write_seconds, pending_bytes
            index, record, diagrams, diagram_bytes = pending.popleft()
            pending_bytes -= diagram_bytes
            started_wait = perf_counter()
            for node, original, future in diagrams:
                try:
                    replaced = future.result()
                except Exception as exc:
                    raise ValueError(f'Record {index}: {type(exc).__name__} while sanitizing diagram.') from None
                if replaced != original:
                    transformer.stats['modified_literals'] += 1
                    node.text = replaced
            write_started = perf_counter()
            if diagrams:
                wait = write_started - started_wait
                transformer.diagram_seconds += wait
                anonymize_seconds += wait
            writer.record(record)
            write_seconds += perf_counter() - write_started
            if executor is not None:
                discard_record(root, record)
            if index % 100_000 == 0:
                elapsed = perf_counter() - started
                print(f'Transformed {index:,} records in {elapsed:.1f} s', file=sys.stderr, flush=True)

        for index, record in enumerate(records(root, reader, retain=executor is not None), 1):
            diagrams = []

            def submit_diagram(node, value):
                diagrams.append((node, value, executor.submit(run_diagram_worker, value)))

            record_started = perf_counter()
            try:
                transformer.record(record, submit_diagram if executor is not None else None)
            except (ValueError, OSError, etree.LxmlError, BadZipFile) as exc:
                raise ValueError(f'Record {index}, type {local(record.tag)}: {type(exc).__name__} while sanitizing payload.') from None
            anonymize_seconds += perf_counter() - record_started
            diagram_bytes = sum(len(original) for _, original, _ in diagrams)
            pending_bytes += diagram_bytes
            pending.append((index, record, diagrams, diagram_bytes))
            while pending:
                first_diagrams = pending[0][2]
                if (len(pending) < 16 and pending_bytes < PENDING_DIAGRAM_BYTES
                        and not all(future.done() for _, _, future in first_diagrams)):
                    break
                write_next()
        while pending:
            write_next()
        stream.write(writer.closing)
    elapsed = perf_counter() - started
    return {
        'xml_read_and_overhead': round(elapsed - anonymize_seconds - write_seconds, 3),
        'anonymize': round(anonymize_seconds, 3),
        'xml_write': round(write_seconds, 3),
    }


def equivalent(left, right):
    if left.tag != right.tag or left.attrib != right.attrib:
        return False
    if (left.text or '') != (right.text or ''):
        if len(left) == 0 or len(right) == 0 or (left.text or '').strip() != (right.text or '').strip():
            return False
    if len(left) != len(right):
        return False
    for a, b in zip(left, right):
        if (a.tail or '').strip() != (b.tail or '').strip() or not equivalent(a, b):
            return False
    return True


class GraphIndex:
    def __init__(self, db):
        self.db = db
        self.db.executescript('''
            PRAGMA journal_mode = OFF;
            PRAGMA synchronous = OFF;
            PRAGMA cache_size = -32768;
            CREATE TABLE definitions (source TEXT PRIMARY KEY, result TEXT NOT NULL UNIQUE);
            CREATE TABLE refs (source TEXT PRIMARY KEY, result TEXT NOT NULL UNIQUE, local INTEGER NOT NULL);
            CREATE TABLE names (result TEXT PRIMARY KEY, source TEXT NOT NULL);
        ''')
        self.batches = {'definitions': {}, 'refs': {}, 'names': {}}

    def remember(self, table, key, fields):
        batch = self.batches[table]
        previous = batch.setdefault(key, fields)
        if previous != fields:
            raise ValueError(f'Inconsistent mapping in {table}.')
        if len(batch) >= 20_000:
            self.flush(table)

    def definition(self, original, changed):
        self.remember('definitions', original, (changed,))

    def reference(self, original, changed, is_local):
        self.remember('refs', original, (changed, is_local))

    def name(self, changed, original):
        self.remember('names', changed, (original,))

    def flush(self, table):
        batch = self.batches[table]
        if not batch:
            return
        statement = {
            'definitions': '''
                INSERT INTO definitions VALUES (?, ?) ON CONFLICT(source) DO UPDATE
                SET result = NULL WHERE result IS NOT excluded.result
            ''',
            'refs': '''
                INSERT INTO refs VALUES (?, ?, ?) ON CONFLICT(source) DO UPDATE
                SET result = NULL WHERE result IS NOT excluded.result OR local IS NOT excluded.local
            ''',
            'names': '''
                INSERT INTO names VALUES (?, ?) ON CONFLICT(result) DO UPDATE
                SET source = NULL WHERE source IS NOT excluded.source
            ''',
        }[table]
        try:
            self.db.executemany(statement, ((key, *batch[key]) for key in sorted(batch)))
        except sqlite3.IntegrityError:
            raise ValueError(f'Pseudonym collision or inconsistent mapping in {table}.') from None
        batch.clear()

    def summary(self):
        for table in self.batches:
            self.flush(table)
        mismatch = self.db.execute('''
            SELECT 1 FROM refs AS r
            LEFT JOIN definitions AS input ON input.source = r.source
            LEFT JOIN definitions AS output ON output.result = r.result
            WHERE input.source IS NOT output.source LIMIT 1
        ''').fetchone()
        if mismatch:
            raise ValueError('An RDF reference changed its target or resolution status.')
        return {
            'unique_rdf_ids': self.db.execute('SELECT count(*) FROM definitions').fetchone()[0],
            'unique_generated_object_names': self.db.execute('SELECT count(*) FROM names').fetchone()[0],
            'local_reference_targets': self.db.execute('SELECT count(*) FROM refs WHERE local').fetchone()[0],
            'local_targets_without_definition_in_both_files': self.db.execute('''
                SELECT count(*) FROM refs LEFT JOIN definitions USING (source)
                WHERE refs.local AND definitions.source IS NULL
            ''').fetchone()[0],
        }


def verify(source, result, transformer):
    root_input, reader_input = open_rdf(source)
    root_output, reader_output = open_rdf(result)
    if root_input.attrib != root_output.attrib or root_input.nsmap != root_output.nsmap:
        raise ValueError('Root XML attributes or namespace bindings differ.')
    expected_pi = [(node.target, node.text) for node in header_instructions(root_input)]
    actual_pi = [(node.target, node.text) for node in header_instructions(root_output)]
    if expected_pi != actual_pi:
        raise ValueError('CIM processing instructions differ.')
    with TemporaryDirectory(prefix='cim-verify-') as directory:
        db = sqlite3.connect(Path(directory) / 'graph.sqlite3')
        try:
            transformer.index = GraphIndex(db)
            pairs = zip_longest(records(root_input, reader_input), records(root_output, reader_output))
            for index, (original, output) in enumerate(pairs, 1):
                if original is None or output is None:
                    raise ValueError('Different record counts.')
                transformer.record(original)
                if not equivalent(original, output):
                    raise ValueError(f'Unexpected XML difference at record {index} ({local(original.tag)}).')
                if index % 100_000 == 0:
                    print(f'Checked {index:,} records', file=sys.stderr, flush=True)
            return transformer.index.summary()
        finally:
            db.close()


def read_translations(path):
    if path is None:
        return {}
    data = json.loads(path.read_text(encoding='utf-8-sig'))
    if not isinstance(data, dict) or not isinstance(data.get('language'), str) or not data['language'].strip():
        raise ValueError('Configuration requires a non-empty language.')
    translations = data.get('translations')
    if not isinstance(translations, dict) or any(
        not key or not isinstance(value, str) or not value.strip()
        for key, value in translations.items()
    ):
        raise ValueError('Configuration requires a translations object with non-empty string values.')
    return translations


def main():
    cli = argparse.ArgumentParser(description='Stream a CIM RDF/XML export and replace identifying values.')
    cli.add_argument('source', type=Path)
    cli.add_argument('output', type=Path)
    cli.add_argument('--key-file', required=True, type=Path, help='Private 32-byte key, created on first use.')
    cli.add_argument('--coordinates', action='store_true', help='Mask geographic coordinates when present.')
    cli.add_argument('--verify', action='store_true', help='Compare an existing output against the input and key.')
    cli.add_argument('--ref-cache-size', type=int, default=200_000, metavar='ENTRIES',
                     help='Maximum cached RDF identifier mappings (default: 200000).')
    cli.add_argument('--fast-diagrams', action='store_true',
                     help='Use faster ZIP compression for diagrams. Use the same option for verification.')
    cli.add_argument('--diagram-workers', type=int, default=1, metavar='COUNT',
                     help='Processes for diagram anonymization during XML generation (default: 1).')
    cli.add_argument('--config', type=Path, help='UTF-8 JSON with language and translations settings.')
    args = cli.parse_args()
    if args.ref_cache_size < 0:
        cli.error('--ref-cache-size must be non-negative')
    if not 1 <= args.diagram_workers <= 16:
        cli.error('--diagram-workers must be between 1 and 16')
    try:
        paths = (args.source, args.output, args.key_file)
        if args.config is not None:
            paths += (args.config,)
        if len({item.resolve() for item in paths}) != len(paths) or any(
            a.exists() and b.exists() and a.samefile(b)
            for index, a in enumerate(paths) for b in paths[index + 1:]
        ):
            raise ValueError('Input, output, key and configuration must be different files.')
        translations = read_translations(args.config)
        started = perf_counter()
        catalog = ModelCatalog.scan(args.source)
        timing = {'catalog': round(perf_counter() - started, 3)}
        print(f"Catalog ready in {timing['catalog']:.1f} s", file=sys.stderr, flush=True)
        engine = Transformer(
            select_key(args.key_file, create=not args.verify), args.coordinates, catalog,
            ref_cache_size=args.ref_cache_size,
            diagram_compression_level=1 if args.fast_diagrams else None,
            translations=translations,
        )
        if args.verify:
            verify_started = perf_counter()
            verification = verify(args.source, args.output, engine)
            timing['verify'] = round(perf_counter() - verify_started, 3)
        else:
            stage = args.output.with_name(args.output.name + '.' + secrets.token_hex(8) + '.part')
            try:
                timing.update(transform(args.source, stage, engine, args.diagram_workers))
                os.replace(stage, args.output)
            finally:
                stage.unlink(missing_ok=True)
            verification = {}
        timing['total'] = round(perf_counter() - started, 3)
        parallel = args.diagram_workers > 1 and not args.verify
        timing['diagram_result_wait' if parallel else 'diagrams_included_in_processing'] = round(engine.diagram_seconds, 3)
        cache = engine.pseudonyms.ref.cache_info()
        print(json.dumps({
            'classes': len(engine.classes), 'records': sum(engine.classes.values()),
            **dict(sorted(engine.stats.items())), **verification,
            'seconds': timing,
            'ref_cache': {'hits': cache.hits, 'misses': cache.misses, 'entries': cache.currsize},
        }, ensure_ascii=False, indent=2))
    except (ValueError, OSError, etree.LxmlError, sqlite3.Error, BadZipFile) as exc:
        cli.exit(1, f'{exc}\n')


if __name__ == '__main__':
    main()
