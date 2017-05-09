module.exports = {
  entry: './src/main',
  devtool: 'source-map',
  output: {
    path: __dirname + '/js',
    filename: 'index.js',
	 library: ['debug_glob'],
  },
  resolve: {
      extensions: ['.webpack.js', '.web.js', '.ts', '.tsx', '.js']
  },
  module: {
      loaders: [
          { test: /\.tsx?$/, loader: 'ts-loader' }
      ]
  }
}
