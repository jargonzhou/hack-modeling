"""
XML files.
"""
import unittest
from xml.etree import ElementTree as ET
import pprint
from . import _DATA_DIR


# pylint: skip-file

class TestParseXML(unittest.TestCase):
  def test_read(self) -> None:
    tree = ET.parse(_DATA_DIR+"/data-text.xml")
    root = tree.getroot()

    all_data = []

    data = root.find("Data")  # find note
    for observation in data:  # type: ignore[union-attr]
      record = {}
      for item in observation:
        lookup_key = list(item.attrib.keys())[0]  # get node's attribute

        if lookup_key == "Numeric":
          rec_key = "NUMERIC"
          rec_value = item.attrib['Numeric']
        else:
          rec_key = item.attrib[lookup_key]
          rec_value = item.attrib['Code']

        record[rec_key] = rec_value
      all_data.append(record)

    pprint.pprint(all_data)
