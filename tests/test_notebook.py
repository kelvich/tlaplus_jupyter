import os
import nbformat

from nbconvert.preprocessors import ExecutePreprocessor
from unittest import TestCase

def run_notebook(notebook_path):
    nb_name, _ = os.path.splitext(os.path.basename(notebook_path))
    dirname = os.path.dirname(notebook_path)

    with open(notebook_path) as f:
        nb = nbformat.read(f, as_version=4)

    proc = ExecutePreprocessor(timeout=600)
    proc.allow_errors = True
    proc.preprocess(nb, {'metadata': {'path': '/'}})
    return [_['outputs'][0] for _ in nb.cells]

class TestNotebook(TestCase):

    def test_notebook(self):
        testnb_path = os.path.join(os.path.dirname(__file__), 'testnb.ipynb')
        outputs = run_notebook(testnb_path)

        for output in outputs:
            self.assertEqual(output['output_type'], 'stream')

        self.assertEqual(outputs[0]['text'], '{<<1, 1>>, <<1, 2>>, <<1, 3>>, <<2, 2>>, <<2, 3>>, <<3, 3>>}')
        self.assertEqual(outputs[1]['text'], '')
        self.assertTrue('97 states generated' in outputs[2]['text'])

